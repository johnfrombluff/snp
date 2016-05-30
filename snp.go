/*******************************************************************************
* PROGRAM:       Simple Notes Processor (snp)                                  *
* AUTHOR:        John Williams <john.williams@otago.ac.nz>		       *
*									       *
* LAST REVISION: Ongoing,   2016					       *
* PREV REVISION: Mon 13 Feb 2013					       *
*									       *
* This program produces PDF files containing lecture notes and slides from a   *
* single source file, via LaTeX with the Beamer package.  There's only one     *
* (OK, two) reason why I wrote it in Go: the notes and slides files can be     *
* compiled in parallel.  (Second: to learn a new language.)		       *
*									       *
* BUGS: None :-) But I could add a few features ... 			       *
*	1. OK, there are some minor bugs. Search for and fix FIXMEs ;-)        *
*									       *
*       2. Move to Markdown syntax, reduce reliance on TeX, so it's possible   *
*          to compile to formats other than PDF (e.g. MS Word?). But can any   *
*	   other option rival the flexibility, accuracy and beauty of TeX?     *
*          Probably not. Also SNP is designed to produce two documents with    *
*          differing structure and formatting from a SINGLE source file.       *
*	   Markdown/Pandoc cannot do that. Pandoc also cannot handle font size *
*	   changes. (Probably not necessary for notes.)  While there is still  *
*	   a need for SNP, it may be beneficial to emit the Notes file in pure *
*	   MD, so that I can distribute an editable format to my students.     *
*									       *
*	   Priorities at this stage for MD conversion are:                     *
*          1. Unicode input and output for TeX. xelatex is not working!        *
*                                                                              *
*          2. Images. PDF for LaTeX, SVG for HTML and PNG for Word. Bitmap     *
*             image quality is currently abysmal.                              *
*                                                                              *
*	   3. Smart entities: fractions (Done for TeX, not thoroughly tested)  *
*                                                                              *
*	   4. Tables. Have implemented simple and pipe, but only reason I      *
*             implemented pipe was for alignment. If I can implement alignment *
*             for simple, then I only need simple and block (for block level   *
*             content in cells, e.g. lists and images.                         *
*                                                                              *
*          5. A format for list of images with text comments (hard)            *
*                                                                              *
*          6. Code cleanup.  Move code to functions, even if used only once.   *
*             Might be a higher priority, and implementing new functionality   *
*             often takes a long time because I don't understand my own code!  *
*                                                                              *
*                                                                              *
*     3.   Perhaps a RADICAL new workflow? Author in MD, export to HTML and    *
*          style with CSS? A separate stylesheet for notes and slides?         *
*          Translation HTML->Word seems to work much better than MD->Word!     *
*          Might get around constant problems with LaTeX tables and alignment? *
*          Also, HTML presentations can (more easily) contain video & audio.   *
*          But: while HTML is great, can MD handle it? Not able to handle      *
*          "complex", tables, i.e. column alignment & block elements in cells. *
*									       *
* FUNCTIONS (in order of appearance in this source file)	               *
*   main								       *
*   debug        convenience function to print debugging messages	       *
*   info         thinnest possible wrapper around fmt.Println		       *
*   error        report error messages with string prefix		       *
*   abort        abort processing and end program gracefully      	       *
*   checkArgs    verifies sanity of arguments				       *
*   readInput    reads a file into a []string				       *
*   writeOutput  writes a string to a file				       *
*   push         convenience function to push a string onto a []string stack   *
*   pop          convenience function to pop a string from a []string stack    *
*   processLines parses the SN markup "language" and converts to LaTeX	       *
*   addGraphics  add an \includegraphics LaTeX command			       *
*   addItem      add an \item						       *
*   addTeXlines  writes LaTeX to notes, slides or both files		       *
*   pushEnv      push a LaTeX environment onto a stack			       *
*   popEnv       pop a LaTeX environment from a stack			       *
*   popEnvs      pop all the environments from the stack		       *
*   writeCommon  write the LaTeX code common to both notes and slides	       *
*   writeNotes   write the LaTeX code for the notes			       *
*   writeSlides  write the LaTeX code for the slides			       *
*   runTeX       run external programs on the generated files		       *
*   runProg      runs a program with arguments on a file                       *
*   baseName     returns a filename minus the extension                        *
*   cleanUp      remove a list of files					       *
*   fileExists   return whether a file exists, and if it does, its size	       *
*   strElide     return the first n characters of a string		       *
*   readConf     read external configuration files and store in Options struct *
*   substr       return the substring between two delimiters, optionally       *
*                including the delimiters                                      *
*									       *
*******************************************************************************/

package main

import (
	"flag"
	"fmt"
	"github.com/dustin/go-humanize"
	"io/ioutil"
	"log"
	"math"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	//	"github.com/mvdan/xurls"
)

const (
	termReset   = 0
	termBold    = 1
	termDim     = 2
	termUl      = 3
	termBlink   = 4
	termRev     = 7
	termBlack   = 0
	termRed     = 1
	termGreen   = 2
	termYellow  = 3
	termBlue    = 4
	termMagenta = 5
	termCyan    = 6
	termWhite   = 7
	termNOOP    = -1
	maxIncludes = 100 // Max number of included files in sn source file
)

// A data structure to hold a key/value pair.
type Pair struct {
	Key   string
	Value uint64
}

// A slice of Pairs that implements sort.Interface to sort by Value.
type PairList []Pair

func (p PairList) Swap(i, j int)      { p[i], p[j] = p[j], p[i] }
func (p PairList) Len() int           { return len(p) }
func (p PairList) Less(i, j int) bool { return p[i].Value < p[j].Value }

// A function to turn a map into a PairList, then sort and return it.
func sortMapByValue(m map[string]uint64) PairList {
	p := make(PairList, len(m))
	i := 0
	for k, v := range m {
		p[i] = Pair{k, v}
		i++
	}
	sort.Sort(p)
	return p
}

var pl PairList

type Options struct {
	Author1           string
	Email1            string
	Author2           string
	Email2            string
	Affiliation       string
	Date              string
	LectureTitle      string
	CourseCode        string
	CourseName        string
	TeXPreambleCommon string
	TeXBeginDocument  string
	notesTeXPreamble  string
	notesTeXBeginDoc  string
	slidesTeXBeginDoc string
	slidesTeXPreamble string
	nupTop            string
	nupBottom         string
	NotesFileName     string
	SlidesFileName    string
	Which             string
	Tab               int
	Indent            int
	hasCitations      bool
	bold              string
	italic            string
}

var o Options

var slidesCount int
var lines []string
var notesTeXlines []string
var slidesTeXlines []string
var markdownLines []string
var envStack []string
var md_line string
var Debug int
var totalSize uint64
var whichToKeep string
var printSizes bool
var run_TeX bool
var del_TeX bool
var leave_alone bool
var fileSizes map[string]uint64
var ErrorText string
var confLocation string
var confFile string
var SlidesOnly bool
var NotesOnly bool
var col_2_w, mp_h string
var line_number int
var indent_level int
var list_type string
var image_used bool
var in_table bool
var table_type string
var pure_MD bool

//var TeXPreambleCommon

func main() {
	info(term("\tWelcome to Simple Notes Processor\t",
		termBold, termYellow, termCyan))

	if !readConf(confFile) {
		abort("Failed to read config file (" + confFile + ")")
	}
	filename, _ := checkArgs(&o)
	lines = readInput(filename)
	processLines(lines)

	n := make(chan bool)
	s := make(chan bool)
	m := make(chan bool)

	//info("====> Input processed <====")
	go writeNotes(filename, n)
	go writeSlides(filename, s)
	go writeMD(filename, m)

	notes := <-n
	slides := <-s
	notes_MD := <-m

	if notes == false || slides == false {
		debug("The LaTeX files have not been deleted.")
	} else {
		//switch whichToKeep {
		if ! del_TeX {
			//case "none":
			//	if notes && slides {
			cleanUp(o.NotesFileName +
				" " + o.SlidesFileName)
			info("\nTeX files deleted")
		} else {
			info("\nTeX files not deleted")
		}

		//case "notes":
		//	cleanUp(o.SlidesFileName)
		//	info("LaTeX slides files deleted.")
		//case "slides":
		//	cleanUp(o.NotesFileName)
		//	info("LaTeX notes files deleted")
		//case "both":
		//	debug("LaTeX files for notes and slides are available.")
		//default:
		//	info("Can't understand which files to keep." +
		//		" ('" + whichToKeep + "')")
		//}
	}
	if notes && slides {
		info(fmt.Sprintf("All done: %d slides produced. Ciao!",
			slidesCount))
		if printSizes {
			if totalSize > 0 {
				fs := sortMapByValue(fileSizes)
				info("\nIncluded file sizes:\n" +
					"   Bytes  Filename")
				info("   -----  --------")
				for i := range fs {
					info(fmt.Sprintf("%8s: %s",
						humanize.Comma(int64(fs[i].Value)),
						filepath.Base(fs[i].Key)))
				}
				info("\nTotal size of included graphics" +
					" files is " +
					humanize.Bytes(totalSize) + ".")
			}
			pdfFile := strings.Replace(o.NotesFileName, ".tex",
				".pdf",
				1)
			_, size := fileExists(pdfFile, "")
			info("Size of notes PDF file is " +
				humanize.Bytes(size) + ".")

			pdfFile = strings.Replace(o.SlidesFileName, ".tex",
				".pdf",
				1)
			_, size = fileExists(pdfFile, "")
			info("Size of slides PDF file is " +
				humanize.Bytes(size) + ".")
		}
	}

	if !notes_MD {
		error("Pandoc encountered an error!", "Bugger")
	}

}

func init() {
	line_number = 0
	indent_level = 0
	slidesCount = 0
	in_table = false
	list_type = ""
	pure_MD = true
	leave_alone = false

	envStack = make([]string, 7) //FIXME: allows nesting up to
	//seven environments. Can I make this a dynamic stack, as
	//opposed to a fixed slice?
	Debug = 0
	totalSize = 0
	whichToKeep = "none"
	printSizes = false
	run_TeX = true
	fileSizes = make(map[string]uint64)
	pl = make(PairList, maxIncludes) // List of included files and sizes
	SlidesOnly = false
	NotesOnly = false
	ErrorText = fmt.Sprintf("\033[%d;%d;%dmError: \033[m",
		termBold, termRed, termCyan)

	confLocation = "/home/john/Dropbox/Writing/snp/"
	confFile = "snp.ini"

	//const (
	//		defaultKeep = "none"
	//		usageKeep   = "Which TeX file to keep (i.e. not delete).\n" +
	//			" Valid values are 'none' (the default)," +
	//			"'both', 'notes' and 'slides'"
	//	)
	//	flag.StringVar(&whichToKeep, "keep", defaultKeep, usageKeep)
	//	flag.StringVar(&whichToKeep, "k", defaultKeep,
	//		usageKeep+"\n(-k is shorthand for -keep)")

	flag.IntVar(&Debug, "d", 0, "Turn debugging output on")
	flag.BoolVar(&printSizes, "s", false, "Print size of included files")
	flag.BoolVar(&run_TeX, "t", true, "Run TeX")
	flag.BoolVar(&del_TeX, "k", false, "Do not delete TeX files after processing them")
}

func term(s string, style int, fg int, bg int) string {
	// Implements ANSI colours in the terminal
	code := fmt.Sprintf("%c[", 0x1B)

	if style != termNOOP {
		code += fmt.Sprintf("%d", style)
	}

	if fg != termNOOP {
		code += fmt.Sprintf(";%d", fg+30)
	}
	if bg != termNOOP {
		code += fmt.Sprintf(";%d", bg+40)
	}
	code += "m" + s + fmt.Sprintf("%c[0m", 0x1B)
	return code

}

func debug(s string) {
	if Debug > 0 {
		fmt.Println(term("Debug:>", termBold, termWhite, termRed) +
			" " + s)
	}
}

func info(s string) {
	fmt.Println(s)
}

func error(s string, e string) {
	info(fmt.Sprintf("%s: %s (%s)",
		term("Error", termNOOP, termWhite, termBlue), s, e))
}

func abort(s string) {
	info("\033[31mFatal error: \033[m: " + s)
	os.Exit(1)
}

func checkArgs(o *Options) (string, uint64) {
	flag.Parse()
	filename := ""

	if len(flag.Args()) < 1 {
		dirname, err := os.Getwd()
		d, err := os.Open(dirname)
		files, err := d.Readdir(-1)
		if err == nil {
			for _, file := range files {
				// FIXME: exclude backup files, so
				// shouldn't end with ~ or start with
				// . or #
				if filepath.Ext(file.Name()) == ".sn" {
					filename = file.Name()
				}
			}
		}
		if Debug < 0 {
			fmt.Fprintf(os.Stderr,
				"No SN input file specified, so using '%s'. \n\n", filename)
		}

		if filename == "" {
			fmt.Println("Usage: %s [inputfile].\n", os.Args[0])
			flag.PrintDefaults()
			os.Exit(2)
		}
	} else {
		filename = flag.Arg(0)
	}

	found, size := fileExists(filename, "")
	if !found {
		abort("Specified file (" + filename + ") not found")
	}

	if Debug > 0 {
		debug("Debugging output on")
	}
	return filename, size
}

/*******************************************************************************
*
* Read a text file and return its contents in a []string
*
*******************************************************************************/
func readInput(filename string) []string {
	if Debug > 1 {
		debug("Scanning the input file (" + filename + ")")
	}
	content, err := ioutil.ReadFile(filename)
	if err != nil {
		log.Fatal(err)
		abort("can't find file: " + filename)
	}

	return strings.Split(string(content), "\n")
}

func writeOutput(filename string, lines string) {
	fo, err := os.Create(filename)
	if err != nil {
		log.Fatal(err)
	}
	defer fo.Close()
	fmt.Fprintln(fo, lines)
}

func push(item string, stack []string) {
	l := len(stack)
	tmp := make([]string, l)
	copy(tmp, stack)
	for i := 0; i < len(stack)-2; i++ {
		stack[i+1] = tmp[i]
	}
	stack[0] = item
}

func pop(stack []string) {
	// FIXME: a warning if there is an attempt to pop an empty stack?
	l := len(stack)
	if l == 0 {
		error("Attempt to pop an empty stack!", "Retard")
	}
	tmp := make([]string, l)
	copy(tmp, stack)
	for i := 0; i < len(stack)-2; i++ {
		stack[i] = tmp[i+1]
	}
}

/*******************************************************************************
*                                                                              *
* Now the functions that process input and transform it to LaTeX.  First, the  *
* source file scanner.                                                         *
*                                                                              *
*******************************************************************************/
func processLines(lines []string) {
	// Read each line and search for switches
	// FIXME: move MD processing to a separate function
	for i := range lines {
		line_number++
		line := lines[i]

		// detect TeX markup
		re_slash := regexp.MustCompile(`\\\w+`)
		re_math := regexp.MustCompile(re_delim("$"))
		if (re_slash.FindStringIndex(line) != nil) || (re_math.FindStringIndex(line) != nil) {
			if Debug > -1 {
				debug("(" + strconv.Itoa(line_number) + ") Found TeX markup: " + line)
			}
			pure_MD = false
		}

		if strings.Contains(line, "\\cite") {
			o.hasCitations = true
		}

		// Save the MD input, then make the line safe for TeX, and translate
		// some character sequences to TeX.
		md_line = line
		line = process_md(line)

		// Split the line at the first space
		keys := strings.SplitN(line, " ", 2)

		// Key is everything before the space, value is everything after
		key := keys[0]
		v := strings.TrimLeft(line, key)
		v = strings.TrimSpace(v)

		// Handle sn comment lines
		if strings.HasPrefix(key, "#") {
			key = "#"
		}

		switch key {
		case "T":
			o.LectureTitle = v
		case "X":
			o.CourseCode = v
		case "N":
			o.CourseName = v
		case "D":
			d, err := strconv.Atoi(v)
			if err == nil {
				Debug = d
				debug("Debugging on")
			} else {
				abort("Could not interpret " + v +
					" as a number")
			}
		case "Z":
			o.Date = "\\date{" + v + "}\n"
			// Extract the year, and compare to current year
			sourceYear := strings.TrimSpace(substr(v, ",", "", false))

			cmd := exec.Command("date", "+%Y")
			output, err := cmd.CombinedOutput()
			thisYear := ""
			if err == nil {
				thisYear = strings.TrimSpace(string(output))
			} else {
				abort("error getting date")
			}
			// Does sourceYear == output?
			aY := sourceYear
			bY := thisYear
			if aY == bY {
				debug("The year in the source file (" + string(aY) + ") agrees with the system date (" + string(bY) + ")\n")
			} else {
				abort("The source file indicates that the year is " + sourceYear + " but the system says that it's " + thisYear + "!\n")
			}
		case "s", "#":
			slidesCount++
			if Debug > 1 {
				fmt.Println("Section: " + v)
			}
			popEnvs()
			pushEnv("section", v)
		case "[bv]":
			leave_alone = true
		case "[ev]":
			leave_alone = false
		case "[soh]":
			SlidesOnly = true
			pushEnv("section", v)
			SlidesOnly = false
		case "i":
			pushEnv("itemize", "")
		case "n":
			pushEnv("enumerate", "")
		case "d":
			pushEnv("description", "")
		case "-", "1.":
			addItem(key, v)
		case "e":
			popEnv(" % manually closed")
		case "g":
			addGraphics(v)
		case "p":
			tmp := NotesOnly
			popEnvs()
			NotesOnly = true
			addTeXlines("\n\\newpage\n")
			NotesOnly = tmp
		case "q":
			pushEnv("quote", v)

		case "t":
			pushEnv("tabular", v)
		case "[slidesonly]", "[so]":
			SlidesOnly = true
			addTeXlines(v + "\n")
			SlidesOnly = false
		case "[sos]":
			SlidesOnly = true
			addTeXlines("\\small\n" + v + "\n")
			SlidesOnly = false
		case "[sof]":
			SlidesOnly = true
			addTeXlines("\\footnotesize\n" + v + "\n")
			SlidesOnly = false
		case "[sol]":
			SlidesOnly = true
			addTeXlines("\\Large\n" + v + "\n")
			SlidesOnly = false
		case "[son]":
			SlidesOnly = true
			addTeXlines("\\normalsize\n" + v + "\n")
			SlidesOnly = false
		case "[sot]":
			SlidesOnly = true
			addTeXlines("\\scriptsize\n" + v + "\n")
			SlidesOnly = false
		case "[slidesonlybegin]", "[sob]":
			SlidesOnly = true
		case "[slidesonlyend]", "[soe]":
			addTeXlines(v)
			SlidesOnly = false
		case "[notesonly]", "[no]":
			NotesOnly = true
			addTeXlines(v)
			NotesOnly = false
		case "[notesonlybegin]", "[nob]":
			NotesOnly = true
		case "[notesonlyend]", "[noe]":
			NotesOnly = false
		case "[nos]":
			NotesOnly = true
			addTeXlines("\\small\n" + v + "\n")
			NotesOnly = false

		case "[preamble]":
			o.TeXPreambleCommon += "\n" + v
		case "tcb":
			tc("begin", v)
			if Debug > -1 {
				info("Found TeX-specific SN code (tc)")
			}
		case "tce":
			tc("end", "")
		case "tcs":
			tc("split", "")
		case ":": // description item. The data is in the previous line though!
			term_label := smart_punc(lines[i-1])
			notesTeXlines[len(notesTeXlines)-1] = ""
			slidesTeXlines[len(slidesTeXlines)-1] = ""
			item := "[" + term_label + "] " + v
			addItem("d", item)
		case "%":
			if in_table && regexp.MustCompile(`-{2,}`).FindStringIndex(md_line) != nil {
				debug("appending: " + md_line + "to markdownLines")
				//reconstruct the bogus colspec
				cols := regexp.MustCompile(`\|`).FindAllStringSubmatch(md_line, -1)
				cols_n := len(cols) + 1
				//colspec := makeColspec(cols)
				//debug("colspec: " + colspec)
				info("Found " + strconv.Itoa(cols_n) + " columns in a pipe table")
				markdownLines = append(markdownLines, md_line+"\n")
			}
		case "#%":
		default: // could be blank or indented
			if line_number == 5002 {
				info("\n\n" + strconv.Itoa(line_number) + " Markdown line: " + md_line)
				info(strconv.Itoa(line_number) + " TeX line     : " + line)
			}

			if in_table && line != "" {
				if table_type == "simple" {
					line = regexp.MustCompile(`\s{2,}`).ReplaceAllString(line, " & ") + "\\\\ "
				} else {
					line = regexp.MustCompile(`\|`).ReplaceAllString(line, " & ") + "\\\\ "
				}
			}
			re_4 := regexp.MustCompile(`^\s{4,}(\-|1\.)`) // at least four spaces at the start of a line, followed by '-' or '1.'
			if re_4.FindStringIndex(line) != nil {
				addItem("", line)
			} else {
				line = strings.TrimSpace(line)
				if len(line) != 0 {
					addTeXlines(line + "\n")
				} else if line == "" {
					popEnv(" % closed by blank line detector")
				} else {
					popEnv(" % closed by top-level parser")
				}
			}
		}
	}
}

/******************************************************************************
 This function handles the inclusion of graphics.  It needs to parse
 arguments given in the source file, which makes it a bit complex ...

 FIXME: allow arbitrary arguments to be passed to \includegraphics
 Currently assumes that there are ONLY one or two integers between the
 delimiters, and the first two are scaling factors. Does no error
 checking.

 FIXME: BUG: does not pass different scaling factors to notes and
 slides files!

******************************************************************************/
func addGraphics(filename string) string {
	f := strings.TrimLeft(filename, "] ")

	notesScale := ""
	slidesScale := ""
	args := ""

	scaling := substr(filename, "[", "]", false)
	f = substr(filename, "]", "", false)
	found, size := fileExists(f, "graphics")
	if !found {
		abort(f + " does not exist")
	} else {
		fileSizes[f] = size
		totalSize += size
	}

	// Write the LaTeX code for the appropriate file(s)
	if scaling == "" { // No scaling supplied
		addTeXlines("\\includegraphics{" + f + "}\n")
	} else {
		scales := strings.Split(scaling, ",")

		if len(scales) == 1 && scales[0] != "" {
			notesScale = scales[0]
			slidesScale = scales[0]
		}
		if len(scales) == 2 {
			slidesScale = scales[1]
			notesScale = scales[0]
		}

		if len(scales) > 2 { // Pass arbitrary args to \includegraphics
			args = scales[2]
		}
		//info( "Scales for graphics file '"+ filename + "' are: " + notesScale + "(Notes); " + slidesScale + " (Slides)" )
		if SlidesOnly == false && NotesOnly == false {
			NotesOnly = true
			addTeXlines("\\includegraphics[scale=" +
				notesScale + "," + args + "]{" + f + "}\n")
			NotesOnly = false

			SlidesOnly = true
			addTeXlines("\\includegraphics[scale=" +
				slidesScale + "," + args + "]{" + f + "}\n")
			SlidesOnly = false
		} else if NotesOnly {
			addTeXlines("\\includegraphics[scale=" +
				notesScale + "," + args + "]{" + f + "}\n")
		} else if SlidesOnly {
			addTeXlines("\\includegraphics[scale=" +
				slidesScale + "," + args + "]{" + f + "}\n")
		}
	}
	return slidesScale
}

func addItem(key string, item string) {
	// This function adds an item to a list. It implements three
	// types: itemize, enumerate and description.
	// FIXME: It seems unreasonably long and complex. Can I factor
	// out the markdown code, or make into (one-use) functions?
	e := ""
	inList := false
	re_k := regexp.MustCompile(`^\s+\-|(\d\.)`) // First non-space item markers

	re_b := regexp.MustCompile(`^\[\s([^\s]+?)\s\]\s+`) // [] Brackets

	//re_n := regexp.MustCompile("^\\s*\\d+\\.")

	// Are we already in a list environment, even if it's not the current one?
	for i := range envStack {
		e = envStack[i]
		if e == "itemize" || e == "enumerate" || e == "description" {
			inList = true
			break
		}
	}

	// Implement Markdown's list type based on list marker. FIXME:
	// currently fails if two successive items have different list
	// markers!
	env := ""
	// Key may be empty if the line starts with a space (i.e. is
	// indented. If it is, make key the first non-space character.

	if key == "" {
		key = re_k.FindString(item)
		//info("Empty key, replaced with '" + key + "'")
	}
	switch key {
	case "-":
		// Search for custom marker
		if re_b.FindAllString(item, -1) != nil {
			image_used = true
			addTeXlines("\\renewcommand\\labelitemi{" + re_b.FindString(item) + "}\n")
			item = re_b.ReplaceAllString(item, "")
		}
		env = "itemize"
	case "n", "1.":
		env = "enumerate"
	case "d":
		env = "description"
	default:
		env = "itemize"
	}

	// Implement Markdown's "four spaces rule" for auto-indentation.
	this_indent_level := indent_level
	re_4 := regexp.MustCompile(`^\s{4,}\-\s|^\s{4,}\d\.\s`) // At
	// least four leading spaces followed by '- ' or '1. '
	re_4 = regexp.MustCompile(`^\s{4,}(\-|1\.)`) // at least four spaces at the start of a line, followed by '-' or '1.'
	pos := re_4.FindStringIndex(item)

	if pos != nil {
		// There are AT LEAST 4 spaces. If there are 8 or
		// more, indent level  is two, and so on.
		// 		info("pos[1] is: " + strconv.Itoa(pos[0]) )
		if pos[1] > 4 && pos[1] < 9 {
			this_indent_level = 1

		} else if pos[1] > 8 && pos[1] < 13 {
			this_indent_level = 2
		} // Only allows three-level lists
		// Trim the list marker, except for description item
		debug("Adding list item: " + item)
		if env != "description" {
			item = item[pos[1]:len(item)]
		}
		debug("Item is now: " + item)

	} else {
		this_indent_level = 0
	}

	//info("Indent level is: " + strconv.Itoa(indent_level) )
	// End Markdown-specific code

	// OK, we know what type of environment the item belongs
	// in. But is it the first item in a child environment?  Or
	// resuming a parent environment?  And do we need to pop just
	// one environment, or more?
	if this_indent_level > indent_level {
		//info("----> pushing " + env)
		pushEnv(env, "  % auto-opened by auto-indenter")
	} else if this_indent_level < indent_level {
		// info("----> popping")
		for this_indent_level < indent_level {
			//info("This indent level: " + strconv.Itoa(this_indent_level) + "; previous indent level: " + strconv.Itoa(indent_level) )
			popEnv(" % auto-closed from auto-indenter")
			indent_level--
		}
	}

	indent_level = this_indent_level

	if inList {
		pushEnv("item", item)
	} else {
		pushEnv(env, "  % auto-opened by list detector")
		addItem(key, item) // recursion!
	}
}

func addTeXlines(s string) {
	if o.Indent < 0 {
		o.Indent = 0
	}
	s = strings.Repeat(" ", o.Tab*o.Indent) + s
	if SlidesOnly && NotesOnly {
		error("Logic bomb on line number "+strconv.Itoa(line_number)+"!", "Notes Only AND Slides Only")
	}
	if SlidesOnly {
		slidesTeXlines = append(slidesTeXlines, s)
	} else if NotesOnly {
		notesTeXlines = append(notesTeXlines, s)
	} else {
		notesTeXlines = append(notesTeXlines, s)
		slidesTeXlines = append(slidesTeXlines, s)
	}

	re_nonMD := regexp.MustCompile(`\[\w+\]`)
	if regexp.MustCompile(`^(\%)`).FindStringIndex(md_line) == nil && SlidesOnly == false {
		// remove processing intructions, e.g. [no]
		if re_nonMD.FindStringIndex == nil {
			info("Found non-Markdown content:" + md_line)
		}
		// FIXME: for some reason, some lines end up repeated
		// in the MD file.  The condition below is a dirty
		// hack until I can find the real reason
		mdl := len(markdownLines)
		if mdl < 1 {
			markdownLines = append(markdownLines, "\n")
			mdl = len(markdownLines)
		}

		if markdownLines[mdl-1] != md_line+"\n" {
			if regexp.MustCompile(`^%`).FindStringIndex(md_line) == nil &&
				regexp.MustCompile(`^p`).FindStringIndex(md_line) == nil {
				md_line = regexp.MustCompile(`^\[no\]`).ReplaceAllString(md_line, "")
				markdownLines = append(markdownLines, md_line+"\n")
			}
		}
	}
}

func pushEnv(env string, content string) {
	lines := ""
	if Debug > 2 {
		info("Pushing: " + env)
	}
	switch env {
	case "section":
		popEnvs()
		o.Indent = 0
		tmp := false
		hasStyle := false
		frameStyle := ""

		if strings.Contains(content, "[") { // Detect the frame style for Beamer slides
			frameStyle = substr(content, "[", "]", false)
			frameStyle = substr(content, "[", "]", true)
			content = strings.TrimRight(content, frameStyle)
			info("Frame contains styling: " + content + frameStyle)
			hasStyle = true
		} else {
			if SlidesOnly {
				frameStyle = "[noframenumbering]"
				hasStyle = true
			}
		}
		if !SlidesOnly {
			tmp = NotesOnly
			NotesOnly = true
			addTeXlines("\n\\section{" + content + "}\n\\normalsize\n")
			NotesOnly = tmp
		}

		tmp = SlidesOnly
		SlidesOnly = true
		addTeXlines("\\end{frame}\n\n" + "\\begin{frame}")
		if hasStyle {
			addTeXlines(frameStyle)
		} else {
			//			addTeXlines("[plain]")
		}
		addTeXlines("\\frametitle{" + content + "}\n")
		SlidesOnly = tmp
	case "item":
		lines = "\\item " + content + "\n"
	case "itemize":
		o.Indent++
		lines = "\\begin{itemize}" + content + "\n"
	case "enumerate":
		o.Indent++
		lines = "\\begin{enumerate}\n"
	case "description":
		o.Indent++
		lines = "\\begin{description}\n"
	case "tabular":
		pushEnv("center", "")
		lines = "\\begin{tabular}" + content + "\n\\toprule\n"
	case "center":
		lines = "\\begin{center}\n" + content + "\n"
	case "quote":
		lines = "\\begin{quote}\n" + content + "\n"
	case "include":
		lines = content + "\n"
	}

	if env == "item" {
		o.Indent++
		addTeXlines(lines)
		o.Indent--
	} else {
		push(env, envStack)
		if env != "section" {
			addTeXlines(lines)
		}
	}
}

func popEnv(message string) {
	env := envStack[0]
	if Debug > 2 {
		info("Popping: " + env)
	}
	s := ""
	o.Indent--

	if env == "tabular" {
		in_table = true
	} else {
		in_table = false
	}

	switch env {
	case "itemize":
		s = "\\end{itemize}" + message + "\n"
		if image_used {
			addTeXlines("\\renewcommand\\labelitemi{-}\n")
			image_used = false
		}
		o.Indent++
	case "enumerate", "description", "tabular", "center", "quote":
		s = ""
		if in_table {
			s = s + "\\bottomrule\n"
			in_table = false
		}
		s = s + "\\end{" + env + "}" + message + "\n"
		o.Indent++
	default:
		if Debug > 1 {
			error("Unknown environment popped!", env)
		}
	}
	pop(envStack)
	if o.Indent < 0 {
		o.Indent = 0
	}
	addTeXlines(s)
	o.Indent--
}

func popEnvs() {
	in_table = false
	l := len(envStack)
	if l > 0 {
		for i := range envStack {
			if len(envStack[i]) != 0 {
				popEnv(" % auto-closed by popEnvs()")
				i++
			}
		}
	}
}
func makeCommon() string {
	h := "\\hypersetup{\n" +
		fmt.Sprintf("    pdftitle    = {%s: %s},\n",
			o.CourseCode, o.CourseName) +
		fmt.Sprintf("    pdfsubject  = {%s},    \n",
			o.LectureTitle) +
		fmt.Sprintf("    pdfkeywords = {%s  %s},\n",
			o.CourseName, o.LectureTitle) +
		fmt.Sprintf("    pdfauthor   = {%s, %s},\n",
			o.Author1, o.Affiliation)

	return (o.TeXPreambleCommon + h + o.TeXBeginDocument)
}

/**************************************************************************
*
* Write the notes file, then run pdflatex and clean up afterwards
*
**************************************************************************/
func writeNotes(filename string, r chan bool) {
	notesTitle := fmt.Sprintf("\\title{%s: %s\\\\%s}\n",
		o.CourseCode, o.CourseName, o.LectureTitle)
	notesAuthor := fmt.Sprintf("\\author{%s\\\\\\href{mailto:%s}{%s}",
		o.Author1, o.Email1, o.Email1)
	if o.Author2 != "" {
		notesAuthor += fmt.Sprintf("\\\\  \\\\ %s\\\\ \\href{mailto:%s}{%s}", o.Author2, o.Email2, o.Email2)
	}
	notesAuthor += "}\n\n"
	notesTop := o.notesTeXPreamble + notesTitle + notesAuthor +
		"\\lfoot{" + o.CourseCode + " (" +
		strings.TrimSpace(o.Date) + ")}\n" +
		//		"\\cfoot{page \\thepage}\n" +
		"\\rfoot{" + o.LectureTitle + "}\n"
	if o.Date != "" {
		notesTop += o.Date
	}

	notesTop += makeCommon() + o.notesTeXBeginDoc
	popEnvs()
	notesBottom := "\n\\printbibliography\n"
	notesBottom += "\\end{document}\n"
	s := notesTop + strings.Join(notesTeXlines, "") + notesBottom

	// The TeX code is done, now write it to a file and run the
	// external tools on it
	fs := strings.Split(filename, ".")

	f := strings.ToLower(fs[0]) + "-notes"
	o.NotesFileName = f + ".tex"
	writeOutput(o.NotesFileName, s)
	if run_TeX {
		info("====> Formatting notes with TeX")
		res := runTeX(f, "notes")
		if res {
			flist := f + ".aux " + f + ".log " +
				f + ".out " + f + ".run.xml " + f + ".bcf"
			if o.hasCitations {
				flist += f + ".bbl " + f + ".blg " + f + ".bcf"
			}
			cleanUp(flist)
		} else {
			info("Because of the previous error, I can't continue processing" +
				" the notes.")
			r <- false
		}
	} else {
		debug("run_TeX is false?!?")
	}
	r <- true
}

/*******************************************************************************
*
* This function writes the LaTeX code for a Beamer presentation, then runs
* pdflatex on it.
*
*******************************************************************************/
func writeSlides(f string, r chan bool) {
	beamerOptions := o.slidesTeXBeginDoc + fmt.Sprintf(
		"\\title{%s}\n"+
			"\\subtitle{%s %s}\n",
		o.LectureTitle, o.CourseCode, o.CourseName)

	if o.Author2 != "" {

		beamerOptions += fmt.Sprintf("\\author{\n"+
			"\\small\n"+
			"\\texorpdfstring{\n"+
			"  \\begin{columns}\n"+
			"    \\column{0.45\\linewidth}\n      \\centering\n"+
			"      %s\\newline\\href{%s}{%s}\n"+
			"    \\column{0.45\\linewidth}\n      \\centering\n"+
			"      %s\\newline\\href{%s}{%s}\n"+
			"  \\end{columns}\n }{Nothing}\n}\n\n",
			o.Author1, o.Email1, o.Email1,
			o.Author2, o.Email2, o.Email2)
	} else {
		beamerOptions += fmt.Sprintf("\\author{%s\n\\newline$<$\\href{mailto:%s}{%s}$>$}\n\n",
			o.Author1, o.Email1, o.Email1)
	}
	beamerOptions += fmt.Sprintf("\\institute{%s}\n", o.Affiliation)
	beamerOptions += "\n\n"

	s := beamerOptions

	s += makeCommon()
	if o.Date != "" {
		s += o.Date
	}
	s += o.slidesTeXPreamble
	popEnvs()
	s += strings.Join(slidesTeXlines, "") + "\\end{frame}\n\\end{document}\n"

	bits := strings.Split(f, ".")
	f = strings.ToLower(bits[0])
	f += "-slides"
	o.SlidesFileName = f + ".tex"
	writeOutput(o.SlidesFileName, s)

	if run_TeX {
		info("====> Formatting slides with TeX")
		res := runTeX(f, "slides")
		if res {
			flist := f + ".log " + f + ".aux " +
				f + ".out " + f + ".nav " + f + ".snm " +
				f + ".toc " + f + ".run.xml " + f + ".bcf"
			if o.hasCitations {
				flist += f + ".bbl " + f + ".blg " + f + ".bcf"
			}
			cleanUp(flist)
		} else {
			info("Because of the previous error, I can't continue processing" +
				" the slides.")
			r <- false
		}
	} else {
		debug("run_TeX is false!?!")
	}
	r <- true
}

/*******************************************************************************
*
* This function writes the Markdown file then runs pandoc on it.
*
*******************************************************************************/

func writeMD(filename string, r chan bool) {
	mdYAML := "---\n"
	notesTitle := fmt.Sprintf("title: %s %s (%s)\n",
		o.CourseCode, o.CourseName, o.LectureTitle)
	notesAuthor := fmt.Sprintf("author: %s", o.Author1)
	if o.Author2 != "" {
		notesAuthor += fmt.Sprintf("and %s", o.Author2)
	}
	notesTop := mdYAML + notesTitle + notesAuthor
	if o.Date != "" {
		d := regexp.MustCompile(`[^\{]+\{([^\}]+)\}`).ReplaceAllString(o.Date, "$1")
		notesTop += "\ndate: " + d
	}
	notesTop = notesTop + "bibliography: /home/john/Dropbox/Writing/bib/all-refs.bib\n\n---\n\n"

	popEnvs()
	notesBottom := "# References"
	s := notesTop + strings.Join(markdownLines, "") + notesBottom
	// The MD code is done, now write it to a file and run the
	// external tools on it
	fs := strings.Split(filename, ".")

	f := strings.ToLower(fs[0]) + "-notes"
	f_m := f + ".md"
	f_h := f + ".html"
	//f_d := f + ".docx"
	writeOutput(f_m, s)
	args_h := []string{"--standalone", "--include-in-header=/home/john/Dropbox/Writing/snp/style.css", "--from=markdown+link_attributes+simple_tables+pipe_tables+definition_lists", "--filter=pandoc-citeproc", "--output=" + f_h, f_m}
	args_d := []string{f_h, "--output=" + f_h}

	res := true
	info("====> Formatting notes with pandoc")
	//info("pandoc " + strings.Join(args_h, " ") )
	res = runProg("pandoc", args_h)
	if res {
		info("pandoc " + strings.Join(args_d, " ") )
		res = runProg("pandoc", args_d)
	} else {
		//fmt.Printf("====> Error running pandoc.\n")
		res = false
	}
	r <- res
}

/*******************************************************************************
*
* This function calls the external tools to produce the PDF files.
*
*******************************************************************************/
func runTeX(f string, ftype string) bool {
	p := "pdflatex"
	p = "xelatex"
	a := []string{"-interaction=nonstopmode", f}
	OK := false
	if runProg(p, a) {
		OK = true
	} else {
		if whichToKeep != ftype {
			switch whichToKeep {
			case "both":
			case "notes":
				whichToKeep = "both"
			case "slides":
				whichToKeep = "both"
			default:
				whichToKeep = ftype
			}
		}
	}

	if OK && o.hasCitations {
		pb := "biber"
		ab := []string{"--quiet", f}
		runProg(pb, ab)
		runProg(p, a)
		cleanUp(f + ".bcf")
	}

	if ftype == "notes" { // Produce the 2up version of the notes
		n := baseName(o.NotesFileName)
		f = n + "-2up.tex"
		t := o.nupTop + "{" + n + ".pdf}\n" + o.nupBottom
		writeOutput(f, t)
		a = []string{"-interaction=nonstopmode", f}
		runProg(p, a)

		flist := n + "-2up.tex " + n + "-2up.aux " + n + "-2up.log "
		cleanUp(flist)
	}
	return true
}

/*******************************************************************************
*                                                                              *
* This function calls an external program with given arguments and a filename  *
* to be processed                                                              *
*                                                                              *
*******************************************************************************/

func runProg(p string, a []string) bool {
	if Debug > 0 {
		debug("\nRunning '" + p + "' '" + strings.Join(a, " ") + "'")
	}

	cmd := exec.Command(p, a...)
	debug("====> About to exec " + p)
	output, err := cmd.CombinedOutput()
	debug("execing of " + p + " has completed\n")
	if err != nil {
		info(ErrorText + p + " did not complete successfully")
		if Debug > 0 {
			fmt.Println("Debug is:", Debug)
		}
		if Debug > 0 {
			info("Parameter to runProg p (program) is: " + p)
			info("Parameter to runProg a (arg) is: " + strings.Join(a, " "))
			fmt.Println("error message is: ", err)
			fmt.Println("error info:", fmt.Sprint(err)+"\nStd out: "+string(output))
		}
		return false
	} else {
		debug("Command '" + p + "' completed succesfully")
		return true
	}
}

func baseName(s string) string {
	fs := strings.Split(s, ".")
	return strings.ToLower(fs[0])
}

/*******************************************************************************
*                                                                              *
* This function removes a list of files given in a string with filenames       *
* separated by spaces                                                          *
*                                                                              *
*******************************************************************************/
func cleanUp(files string) {
	flist := strings.Fields(files)
	for i := 0; i < len(flist); i++ {
		exists, _ := fileExists(flist[i], "")
		if exists {
			err := os.Remove(flist[i])

			if err == nil {
				if Debug > 2 {
					info("Successfully removed " + files)
				}
			} else {
				fmt.Println("Error removing files: ", err)
			}
		}
	}
}

/*******************************************************************************
*                                                                              *
* This function checks for the existence of a file                             *
*                                                                              *
*******************************************************************************/
func fileExists(filename string, t string) (bool, uint64) {
	graphicsTypes := []string{"", ".pdf", ".jpg", ".jpeg", ".png"}
	found := false
	f := filename
	s, _ := os.Stat(f)

	if t == "graphics" {
		for i := range graphicsTypes {
			f = filename + graphicsTypes[i]
			stat, err := os.Stat(f)
			if err == nil {
				found = true
				s = stat
				break
			}
		}
	} else {
		stat, err := os.Stat(filename)
		if err == nil {
			found = true
			s = stat
		}
	}

	if found {
		return true, uint64(s.Size())
	} else {
		return false, uint64(0)
	}
	return found, uint64(0)
}

func strElide(s string, l int) string {
	end := math.Min(float64(len(s)), float64(l))
	e := int(end)
	return (s[0:e])
}

func readConf(filename string) bool {
	o.Date = ""
	o.hasCitations = false
	o.Indent = 0

	if Debug > 0 {
		info("Reading configuration from files in '" +
			confLocation + "'")
	}

	contents := readInput(confLocation + filename)
	key := ""
	val := ""

	for i := range contents {
		if contents[i] == "" {
			break
		}
		keyval := strings.Split(contents[i], " = ")
		key = strings.Trim(keyval[0], " ")
		val = strings.Trim(keyval[1], " ")
		// Handle sn comment lines
		if strings.HasPrefix(key, "#") {
			key = "#"
		}

		switch key {
		case "Author1":
			o.Author1 = val
		case "Author2":
			o.Author2 = val
		case "Affiliation":
			o.Affiliation = val
		case "Email1":
			o.Email1 = val
		case "Email2":
			o.Email2 = val
		case "ErrorText":
			ErrorText = val
		case "Tab":
			o.Tab, _ = strconv.Atoi(val)
		case "Indent":
			o.Indent, _ = strconv.Atoi(val)
		case "bold":
			o.bold = val
		case "italic":
			o.italic = val
		case "#":
		default:
			error("No match for key in snp.ini! Key is: "+key, "")
		}
	}

	TeXOptions := readInput(confLocation + "TeXOptions")
	lines := ""
	curKey := ""
	prevKey := ""
	for i := range TeXOptions {
		tokens := strings.Split(TeXOptions[i], ":")
		if len(tokens) > 1 {
			curKey = strings.Trim(tokens[0], " ")
			switch prevKey {
			case "TeXBeginDocument":
				o.TeXBeginDocument = lines
			case "TeXPreambleCommon":
				o.TeXPreambleCommon = lines
			case "notesTeXPreamble":
				o.notesTeXPreamble = lines
			case "notesTeXBeginDocument":
				o.notesTeXBeginDoc = lines
			case "slidesTeXPreamble":
				o.slidesTeXPreamble = lines
			case "slidesTeXBeginDoc":
				o.slidesTeXBeginDoc = lines
			case "nupTop":
				o.nupTop = strings.TrimSpace(lines)
			case "nupBottom":
				o.nupBottom = lines
			}
			lines = ""
		} else {
			prevKey = curKey
			lines += tokens[0] + "\n"
		}
	}
	return true
}

/************************************************************************
* Returns string between two delimiters, optionally including the       *
* delimeters themselves.  If the end string is "", returns from the     *
* start delimiter to the end of the input string                        *
************************************************************************/
func substr(s, start, end string, id bool) string {
	x := strings.Index(s, start)
	y := 0

	if end == "" {
		y = len(s)
	} else {
		y = strings.Index(s, end)
	}
	var ss string

	if id { // id = "include delimiters"
		ss = s[x : y+1]
	} else {
		ss = s[x+1 : y]
	}
	if Debug > 2 {
		info("Substring of '" + s + "' delimited by '" +
			start + "' and '" + end + "' is '" + ss + "'")
	}
	return strings.TrimSpace(ss)
}

func tc(part, pars string) {
	// Mimics a two-column table by laying out two minipages side-by side. Use the height field to stop the minipages floating over text.
	parv := strings.Split(pars, " ") // Minipage height + width of left column

	switch part {
	case "begin":
		// FIXME: check that values are integer and float
		mp_h = strings.TrimSpace(parv[1])
		col_1_w := strings.TrimSpace(parv[0])
		w, e := strconv.ParseFloat(col_1_w, 2)
		if e != nil {
			//FIXME: use the error code!
			error("Error:", "How to convert error object to string?")
		}
		col_2_w = strconv.FormatFloat(1-w-0.10, 'f', 2, 64) // WTF?
		//info("Column widths are " + col_1_w + " and " + col_2_w + "; height: " + mp_h)

		addTeXlines("   \\begin{minipage}[b][" + mp_h + "cm][t]{" + col_1_w + "\\linewidth}\n")
	case "split":
		//info("Split of two-column layout")
		addTeXlines(" \\end{minipage}\n")
		addTeXlines("   \\begin{minipage}[b][" + mp_h + "cm][t]{" + col_2_w + "\\linewidth}\n")
	case "end":
		//info("End two-column layout")
		addTeXlines(" \\end{minipage}\n\n")
	}
}

func parseCitations(line string) string {
	re := regexp.MustCompile("@(\\w+)")
	cites := re.FindAllString(line, -1)
	debug("Found citation keys:" + strings.Join(cites, " "))
	s := strings.Join(cites, ",")
	re = regexp.MustCompile("@")
	s = re.ReplaceAllString(s, "")
	debug("Returning " + s)
	return (s)
}

func append(slice []string, element string) []string {
	n := len(slice)
	if n == cap(slice) {
		// Slice is full; must grow.
		// We double its size and add 1, so if the size is zero we still grow.
		newSlice := make([]string, len(slice), 2*len(slice)+1)
		copy(newSlice, slice)
		slice = newSlice
	}
	slice = slice[0 : n+1]
	slice[n] = element
	return slice
}

func smart_punc(line string) string {
	// "Smart" punctuation, i.e. handling quotation marks,
	// ellipses, percentage signs and ampersands in the TeX-safe
	// way.
	// "Smart" punctuation, i.e. translate to TeX and escape TeX
	re_el := regexp.MustCompile(`\.\.\.`) // ellipsis
	line = re_el.ReplaceAllString(line, "\\ldots")

	re_qo := regexp.MustCompile("([\\s\\(])\"") // open quotation mark
	line = re_qo.ReplaceAllString(line, "$1``")

	re_qc := regexp.MustCompile("([^\"])\"") // close quotation mark
	line = re_qc.ReplaceAllString(line, "$1''")

	re_pc := regexp.MustCompile("(\\d|\\?)\\%") // escape '%'. FIXME: match anywhere except start of line.
	line = re_pc.ReplaceAllString(line, "$1\\%")

	re_ss := regexp.MustCompile(re_delim("^")) // Superscript (in-text)
	line = re_ss.ReplaceAllString(line, "\\textsuperscript{$1}")

	//re_dol := regexp.MustCompile("\\$(?P<amt>\\d+(\\.\\d{2}))*[\\s\\.][^\\$]")   // escape $
	re_dol := regexp.MustCompile(`\$(\d)`) // escape $
	if re_dol.FindStringIndex(line) != nil {
		debug("Found $: " + line)
		line = re_dol.ReplaceAllString(line, "\\$$1")
	}

	re_frac := regexp.MustCompile(` (\d+)/(\d+) `) // TeX-ify fraction
	line = re_frac.ReplaceAllString(line, "$\\frac{$1}{2}$")

	re_amp := regexp.MustCompile("\\&")  // escape &  FIXME: breaks math array environment!
	re_uri := regexp.MustCompile("http") // detect URI
	if re_amp.FindStringIndex(line) != nil && re_uri.FindStringIndex(line) == nil {
		if envStack[0] != "tabular" && leave_alone != true { // Or array?
			debug("Current environment: " + envStack[0])
			line = re_amp.ReplaceAllString(line, " \\& ")
		}
	}
	return (line)
}

func re_delim(delim string) string {
	// Anything that isn't a delimiter between two delimiters.
	s := `\` + delim + `([^\` + delim + `]+)\` + delim
	//info(s)
	return (s)
}

func makeColspec(cols [][]string) string {
	colspec := "[t]{"
	//info("Cols: ")
	//fmt.Printf("%v",cols)
	//info("\n")
	for _, col := range cols {
		if regexp.MustCompile(`:-`).FindStringIndex(col[0]) != nil {
			colspec = colspec + " l"
		} else if regexp.MustCompile(`-:`).FindStringIndex(col[0]) != nil {
			colspec = colspec + " r"
		} else {
			colspec = colspec + " l"
		}
	}
	colspec = colspec + " }"
	return (colspec)
}

func processTables(line string) string {
	// Process Markdown tables, both simple and pipe.
	// Detect different types of Pandoc tables
	// Difficult because a line of dashes indicates a table, but
	// the header information is in the previous line. Also, have
	// to discard the line that contains the dashes!
	re_simp := regexp.MustCompile(`(:*-{2,}:*)\s+`)
	re_pipe := regexp.MustCompile(`^\|`)
	re_blok := regexp.MustCompile(`^\+\-`)

	line += " "
	cols := [][]string{}
	if re_simp.FindStringIndex(line) != nil {
		info("Found simple table!")
		table_type = "simple"
		cols = re_simp.FindAllStringSubmatch(line, -1)
	} else if re_pipe.FindStringIndex(line) != nil && table_type != "block" {
		info("Found pipe table!")
		table_type = "pipe"
		cols = regexp.MustCompile(`\|`).FindAllStringSubmatch(line, -1)
	} else if re_blok.FindStringIndex(line) != nil {
		// Could be the first OR last line of the table
		if table_type == "block" {
			info(strconv.Itoa(line_number) + ": End of block table")
			table_type = "none"
		} else {
			info(strconv.Itoa(line_number) + ": Found block table")
			table_type = "block"
			cols = regexp.MustCompile(`\+`).FindAllStringSubmatch(line, -1)
		}
	}
	cols_n := len(cols)
	if cols_n > 0 {
		in_table = true
		info("Found table with " + strconv.Itoa(len(cols)) + " columns")
		debug(line)
		colspec := makeColspec(cols)
		info("colspec: " + colspec)
		has_header := false

		// Remove the previous line from the TeX output file, because we need
		// to re-process it. FIXME: true for simple, what about pipe and block?
		header := ""
		if table_type == "simple" {
			header = smart_punc(lines[line_number-2])
			notesTeXlines[len(notesTeXlines)-1] = ""
			slidesTeXlines[len(slidesTeXlines)-1] = ""
			debug("header:" + header)
		} else {
			// The header of a pipe or block table may be empty
			if regexp.MustCompile(`^[\|\s]+$`).FindStringIndex(lines[line_number]) == nil {
				header = smart_punc(lines[line_number])
			} else {
				debug("Blank header line in pipe table")
				header = ""
			}
		}

		if header != "" {
			has_header = true
		} else {
			has_header = false
		}

		pushEnv("tabular", colspec)
		if has_header {
			if table_type == "simple" {
				// FIXME: adds extra & at end of line (?)
				header = regexp.MustCompile(`\s{2,}`).ReplaceAllString(header, " & ")
			} else if table_type == "pipe" {
				header = regexp.MustCompile(`\|`).ReplaceAllString(header, " & ")
			} else if table_type == "block" {
				header = regexp.MustCompile(`[\|]`).ReplaceAllString(header, " & ")
			}

			addTeXlines(header)
			addTeXlines("\\\\\n\\midrule\n")
		}
		// Now discard the line with --- indicating the table
		debug("Discarding line: " + line)
		line = "%" // Can't replace with a blank line: it will end the table env.
	} else if in_table {
		if regexp.MustCompile(`:-|-:`).FindStringIndex(line) != nil {
			//info("Found pipe table column specification: '" + line + "'")
			line = "%"
		}
		debug("The subsequent lines are: " + line )
	}
	return(line)
}

func process_md(line string) string {
	line = smart_punc(line)
	// Set up regular expressions for line parsing
	match_string := `([^\` + o.bold + `]+)`
	bold_re := `\` + o.bold + `{2}` + match_string + `\` + o.bold + `{2}`
	ital_re := `\` + o.bold + `{1}` + match_string + `\` + o.bold + `{1}`

	// Markdown processing
	// Emphasis
	re_b := regexp.MustCompile(bold_re) // Bold
	re_i := regexp.MustCompile(ital_re) // italics

	// Links, URIs and images. FIXME: deal with ) in URI
	re_g := regexp.MustCompile(`!\[(?P<text>[^\]]*)\](\((?P<path>[^\)]+)\))*(\{(?P<arguments>[^\}]*)\))*`) // graphics
	// source: http://daringfireball.net/2010/07/improved_regex_for_matching_urls

	re_uri := `(?i)\b((?:[a-z][\w-]+:(?:/{1,3}|[a-z0-9%])|www\d{0,3}[.]|[a-z0-9.\-]+[.][a-z]{2,4}/)(?:[^\s()<>]+|\(([^\s()<>]+|(\([^\s()<>]+\)))*\))+(?:\(([^\s()<>]+|(\([^\s()<>]+\)))*\)|[^\s!()\[\]{};:'",<>?«»“”‘’]))`

	re_h := regexp.MustCompile(`\[(?P<text>[^\]]+)\]\((?P<uri>` + re_uri + `)\)`) // link

	re_keyval := regexp.MustCompile(`(?P<key>\w+)\=(?P<value>[^,]+)`)
	re_bogus := regexp.MustCompile(`align=center`)
	found := false

	// Scan line for Markdown markup
	if re_b.FindStringIndex(line) != nil {
		line = re_b.ReplaceAllString(line, "\\textbf{$1}")
		found = true
	}
	if re_i.FindStringIndex(line) != nil {
		line = re_i.ReplaceAllString(line, "\\textit{$1}")
		found = true
	}
	if re_h.FindStringIndex(line) != nil {
		line = re_h.ReplaceAllString(line, "\\href{$uri}{$text}")
		found = true
	}

	// Process graphics links
	if re_g.FindStringIndex(line) != nil {
		// \\begin{center}\n  \\end{center}\n"
		// FIXME: I need to remove invalid argument for includegraphics
		md := map[string]string{}
		n1 := re_g.SubexpNames()
		r1 := re_g.FindAllStringSubmatch(line, -1)[0]
		for i, n := range r1 {
			if n1[i] == "arguments" && n != "" {
				r2 := re_keyval.FindAllStringSubmatch(n, -1)
				for _, pair := range r2 {
					key := pair[1]
					value := pair[2]
					if key == "align" && value == "center" {
						//info("Auto-centering")
						//info("before: " + line)
						line = re_bogus.ReplaceAllString(line, "")
						//info("after: " + line)
						pushEnv("center", "")
					}

				}
			}
			md[n1[i]] = n
		}
		line = re_g.ReplaceAllString(line, "\n\\includegraphics[$arguments]{$path}\n")
		// FIXME: Dirty hack. Whatever the extension
		// is, remove it and substitute PDF for
		// TeX. But what if I really want to include a
		// PNG?
		line = regexp.MustCompile(`\.svg`).ReplaceAllString(line, ".pdf")
		fmt.Println(line)
		found = true
	}

	// No return value ?
	processTables(line)
	if regexp.MustCompile(`:*-{2,}\s+:*`).FindStringIndex(line) != nil {
		debug("should be gone: " +line)
		line = "%"
	}

	// Citations
	re_p := regexp.MustCompile(`\[(?P<prefix>[^@]*)(?P<key>(@[^\[]+);*)+\s*(?P<suffix>[^\]]*)\]`) // Parenthesised citation
	re_t := regexp.MustCompile(`@(?P<key>[\w\.]+)\s{0,1}(\[(?P<suffix>[^\}]+)\])*`)               //in-text citation
	if re_p.FindStringIndex(line) != nil {
		cites := parseCitations(line)
		line = re_p.ReplaceAllString(line, "\\citep[$prefix][$suffix]{"+cites+"}")
		o.hasCitations = true
		found = true
	} else {
		if re_t.FindStringIndex(line) != nil {
			cites := parseCitations(line)
			line = re_t.ReplaceAllString(line, "\\citet[$suffix]{"+cites+"}")
			o.hasCitations = true
			found = true
		}
	}

	if found {
		if Debug > 0 {
			debug("Formatted line:   " + line)
		}
		found = false
	}
	// End Markdown scanning
	return line
}

// Local variables:
// mode: go
// compile-command: "go build"
// End:
