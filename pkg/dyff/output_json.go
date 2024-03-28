// Copyright © 2019 The Homeport Team
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.

package dyff

import (
	"bufio"
	"bytes"
	"crypto/x509"
	"encoding/base64"
	"encoding/hex"
	"encoding/pem"
	"fmt"
	"io"
	"math"
	"strings"

	"github.com/gonvenience/bunt"
	"github.com/gonvenience/term"
	"github.com/gonvenience/text"
	"github.com/gonvenience/ytbx"
	"github.com/lucasb-eyer/go-colorful"
	"github.com/sergi/go-diff/diffmatchpatch"
	yamlv3 "gopkg.in/yaml.v3"
)

// JsonReport is a reporter with human readable output in mind
type JsonReport struct {
	Report
	MinorChangeThreshold  float64
	MultilineContextLines int
	NoTableStyle          bool
	DoNotInspectCerts     bool
	OmitHeader            bool
	UseGoPatchPaths       bool
}

// WriteReport writes a human readable report to the provided writer
func (report *JsonReport) WriteReport(out io.Writer) error {
	writer := bufio.NewWriter(out)
	defer writer.Flush()

	// Only show the document index if there is more than one document to show
	showPathRoot := len(report.From.Documents) > 1

	// Show banner if enabled
	if !report.OmitHeader {
		var header = fmt.Sprintf(`     _        __  __
   _| |_   _ / _|/ _|  between %s
 / _' | | | | |_| |_       and %s
| (_| | |_| |  _|  _|
 \__,_|\__, |_| |_|   returned %s
        |___/
`,
			ytbx.HumanReadableLocationInformation(report.From),
			ytbx.HumanReadableLocationInformation(report.To),
			bunt.Style(text.Plural(len(report.Diffs), "difference"), bunt.Bold()))

		_, _ = writer.WriteString(bunt.Style(
			header,
			bunt.ForegroundFunc(func(x int, _ int, _ rune) *colorful.Color {
				switch {
				case x < 7:
					return &colorful.Color{R: .45, G: .71, B: .30}

				case x < 13:
					return &colorful.Color{R: .79, G: .76, B: .38}

				case x < 21:
					return &colorful.Color{R: .65, G: .17, B: .17}
				}

				return nil
			}),
		))
	}

	// Loop over the diff and generate each report into the buffer
	for _, diff := range report.Diffs {
		if err := report.generateHumanDiffOutput(writer, diff, report.UseGoPatchPaths, showPathRoot); err != nil {
			return err
		}
	}

	// Finish with one last newline so that we do not end next to the prompt
	_, _ = writer.WriteString("\n")
	return nil
}

// generateHumanDiffOutput creates a human readable report of the provided diff and writes this into the given bytes buffer. There is an optional flag to indicate whether the document index (which documents of the input file) should be included in the report of the path of the difference.
func (report *JsonReport) generateHumanDiffOutput(output stringWriter, diff Diff, useGoPatchPaths bool, showPathRoot bool) error {
	_, _ = output.WriteString("\n")
	_, _ = output.WriteString(pathToString(diff.Path, useGoPatchPaths, showPathRoot))
	_, _ = output.WriteString("\n")

	blocks := make([]string, len(diff.Details))
	for i, detail := range diff.Details {
		generatedOutput, err := report.generateHumanDetailOutput(detail)
		if err != nil {
			return err
		}

		blocks[i] = generatedOutput
	}

	// For the use case in which only a path-less diff is suppose to be printed,
	// omit the indent in this case since there is only one element to show
	indent := 2
	if diff.Path != nil && len(diff.Path.PathElements) == 0 {
		indent = 0
	}

	report.writeTextBlocks(output, indent, blocks...)
	return nil
}

// generateHumanDetailOutput only serves as a dispatcher to call the correct sub function for the respective type of change
func (report *JsonReport) generateHumanDetailOutput(detail Detail) (string, error) {
	switch detail.Kind {
	case ADDITION:
		return report.generateHumanDetailOutputAddition(detail)

	case REMOVAL:
		return report.generateHumanDetailOutputRemoval(detail)

	case MODIFICATION:
		return report.generateHumanDetailOutputModification(detail)

	case ORDERCHANGE:
		return report.generateHumanDetailOutputOrderchange(detail)
	}

	return "", fmt.Errorf("unsupported detail type %c", detail.Kind)
}

func (report *JsonReport) generateHumanDetailOutputAddition(detail Detail) (string, error) {
	var output bytes.Buffer

	switch detail.To.Kind {
	case yamlv3.SequenceNode:
		_, _ = output.WriteString(yellow("%c %s added:\n",
			ADDITION,
			text.Plural(len(detail.To.Content), "list entry", "list entries"),
		))

	case yamlv3.MappingNode:
		_, _ = output.WriteString(yellow("%c %s added:\n",
			ADDITION,
			text.Plural(len(detail.To.Content)/2, "map entry", "map entries"),
		))
	}

	ytbx.RestructureObject(detail.To)
	yamlOutput, err := yamlStringInGreenishColors(detail.To)
	if err != nil {
		return "", err
	}

	report.writeTextBlocks(&output, 2, yamlOutput)

	return output.String(), nil
}

func (report *JsonReport) generateHumanDetailOutputRemoval(detail Detail) (string, error) {
	var output bytes.Buffer

	switch detail.From.Kind {
	case yamlv3.DocumentNode:
		_, _ = fmt.Fprint(&output, yellow("%c %s removed:\n",
			REMOVAL,
			text.Plural(len(detail.From.Content), "document"),
		))

	case yamlv3.SequenceNode:
		text := text.Plural(len(detail.From.Content), "list entry", "list entries")
		_, _ = output.WriteString(yellow("%c %s removed:\n", REMOVAL, text))

	case yamlv3.MappingNode:
		text := text.Plural(len(detail.From.Content)/2, "map entry", "map entries")
		_, _ = output.WriteString(yellow("%c %s removed:\n", REMOVAL, text))
	}

	ytbx.RestructureObject(detail.From)
	yamlOutput, err := yamlStringInRedishColors(detail.From)
	if err != nil {
		return "", err
	}

	report.writeTextBlocks(&output, 2, yamlOutput)

	return output.String(), nil
}

func (report *JsonReport) generateHumanDetailOutputModification(detail Detail) (string, error) {
	var output bytes.Buffer
	fromType := humanReadableType(detail.From)
	toType := humanReadableType(detail.To)

	switch {
	case fromType == "string" && toType == "string":
		// delegate to special string output
		report.writeStringDiff(
			&output,
			detail.From.Value,
			detail.To.Value,
		)

	case fromType == "binary" && toType == "binary":
		from, err := base64.StdEncoding.DecodeString(detail.From.Value)
		if err != nil {
			return "", err
		}

		to, err := base64.StdEncoding.DecodeString(detail.To.Value)
		if err != nil {
			return "", err
		}

		_, _ = output.WriteString(yellow("%c content change\n", MODIFICATION))
		report.writeTextBlocks(&output, 0,
			red("%s", createStringWithPrefix("  - ", hex.Dump(from))),
			green("%s", createStringWithPrefix("  + ", hex.Dump(to))),
		)

	default:
		if fromType != toType {
			_, _ = output.WriteString(yellow("%c type change from %s to %s\n",
				MODIFICATION,
				italic(fromType),
				italic(toType),
			))

		} else {
			_, _ = output.WriteString(yellow("%c value change\n",
				MODIFICATION,
			))
		}

		from, err := yamlString(detail.From)
		if err != nil {
			return "", err
		}

		to, err := yamlString(detail.To)
		if err != nil {
			return "", err
		}

		_, _ = output.WriteString(red("%s", createStringWithPrefix("  - ", strings.TrimRight(from, "\n"))))
		_, _ = output.WriteString(green("%s", createStringWithPrefix("  + ", strings.TrimRight(to, "\n"))))
	}

	return output.String(), nil
}

func (report *JsonReport) generateHumanDetailOutputOrderchange(detail Detail) (string, error) {
	var output bytes.Buffer

	_, _ = output.WriteString(yellow("%c order changed\n", ORDERCHANGE))
	switch detail.From.Kind {
	case yamlv3.SequenceNode:
		asStringList := func(sequenceNode *yamlv3.Node) ([]string, error) {
			result := make([]string, len(sequenceNode.Content))
			for i, entry := range sequenceNode.Content {
				result[i] = entry.Value
				if entry.Value == "" {
					s, err := yamlString(entry)
					if err != nil {
						return result, err
					}
					result[i] = s
				}
			}

			return result, nil
		}

		from, err := asStringList(detail.From)
		if err != nil {
			return "", err
		}
		to, err := asStringList(detail.To)
		if err != nil {
			return "", err
		}

		const singleLineSeparator = ", "

		threshold := term.GetTerminalWidth() / 2
		fromSingleLineLength := stringArrayLen(from) + ((len(from) - 1) * plainTextLength(singleLineSeparator))
		toStringleLineLength := stringArrayLen(to) + ((len(to) - 1) * plainTextLength(singleLineSeparator))
		if estimatedLength := max(fromSingleLineLength, toStringleLineLength); estimatedLength < threshold {
			_, _ = output.WriteString(red("  - %s\n", strings.Join(from, singleLineSeparator)))
			_, _ = output.WriteString(green("  + %s\n", strings.Join(to, singleLineSeparator)))

		} else {
			_, _ = output.WriteString(CreateTableStyleString(" ", 2,
				red("%s", strings.Join(from, "\n")),
				green("%s", strings.Join(to, "\n"))))
		}
	}

	return output.String(), nil
}

func (report *JsonReport) writeStringDiff(output stringWriter, from string, to string) {
	fromCertText, toCertText, err := report.LoadX509Certs(from, to)

	switch {
	case err == nil:
		_, _ = output.WriteString(yellow("%c certificate change\n", MODIFICATION))
		_, _ = output.WriteString(report.highlightByLine(fromCertText, toCertText))

	case isWhitespaceOnlyChange(from, to):
		_, _ = output.WriteString(yellow("%c whitespace only change\n", MODIFICATION))
		report.writeTextBlocks(output, 0,
			red("%s", createStringWithPrefix("  - ", showWhitespaceCharacters(from))),
			green("%s", createStringWithPrefix("  + ", showWhitespaceCharacters(to))),
		)

	case isMultiLine(from, to):

		// create line by line diff
		dmp := diffmatchpatch.New()
		oldIdx, newIdx, lines := dmp.DiffLinesToChars(from, to)
		diff := dmp.DiffMain(oldIdx, newIdx, false)
		diff = dmp.DiffCharsToLines(diff, lines)

		var ins, del int
		var buf bytes.Buffer
		multilineContextLines := report.MultilineContextLines
		for _, d := range diff {
			// color and format each diff by type
			switch d.Type {
			case diffmatchpatch.DiffInsert:
				fmt.Fprint(&buf, green(createStringWithContinuousPrefix("  + ", d.Text)))
				ins++

			case diffmatchpatch.DiffDelete:
				fmt.Fprint(&buf, red(createStringWithContinuousPrefix("  - ", d.Text)))
				del++

			case diffmatchpatch.DiffEqual:
				// skip eqaul output if requested context is 0 or the equal text is empty
				if multilineContextLines <= 0 || len(d.Text) == 0 {
					continue
				}
				// add amount of unchanged lines as configured
				lines := strings.Split(d.Text, "\n")
				lower := int(math.Min(float64(len(lines)), float64(multilineContextLines)))
				upper := len(lines) - multilineContextLines
				// if string ends with \n we need to display one more line on the upper limit
				if strings.HasSuffix(d.Text, "\n") {
					upper--
				}
				var val string
				if upper <= lower {
					val = strings.Join(lines, "\n")
				} else {
					val = fmt.Sprintf("%s\n\n[%s unchanged)]\n\n%s",
						strings.Join(lines[:lower], "\n"),
						text.Plural((upper-lower), "line"),
						strings.Join(lines[upper:], "\n"))
				}
				fmt.Fprint(&buf, dimgray(createStringWithContinuousPrefix("    ", val)))
			}
		}
		_, _ = output.WriteString(
			yellow("%c value change in multiline text (%s, %s)\n",
				MODIFICATION, text.Plural(ins, "insert"), text.Plural(del, "deletion")))
		_, _ = output.WriteString(buf.String())
		_, _ = output.WriteString("\n")

	case isMinorChange(from, to, report.MinorChangeThreshold):
		_, _ = output.WriteString(yellow("%c value change\n", MODIFICATION))
		diffs := diffmatchpatch.New().DiffMain(from, to, false)
		_, _ = output.WriteString(highlightRemovals(diffs))
		_, _ = output.WriteString(highlightAdditions(diffs))

	default:
		_, _ = output.WriteString(yellow("%c value change\n", MODIFICATION))
		_, _ = output.WriteString(red("%s", createStringWithPrefix("  - ", from)))
		_, _ = output.WriteString(green("%s", createStringWithPrefix("  + ", to)))
	}
}

func (report *JsonReport) highlightByLine(from, to string) string {
	fromLines := strings.Split(from, "\n")
	toLines := strings.Split(to, "\n")

	var buf bytes.Buffer

	if len(fromLines) == len(toLines) {
		for i := range fromLines {
			if fromLines[i] != toLines[i] {
				fromLines[i] = red(fromLines[i])
				toLines[i] = green(toLines[i])

			} else {
				fromLines[i] = lightred(fromLines[i])
				toLines[i] = lightgreen(toLines[i])
			}
		}

		report.writeTextBlocks(&buf, 0,
			createStringWithPrefix(red("  - "), strings.Join(fromLines, "\n")),
			createStringWithPrefix(green("  + "), strings.Join(toLines, "\n")))

	} else {
		report.writeTextBlocks(&buf, 0,
			red("%s", createStringWithPrefix("  - ", from)),
			green("%s", createStringWithPrefix("  + ", to)),
		)
	}

	return buf.String()
}

// LoadX509Certs tries to load the provided strings as a cert each and returns
// a textual representation of the certs, or an error if the strings are not
// X509 certs
func (report *JsonReport) LoadX509Certs(from, to string) (string, string, error) {
	// Back out quickly if cert inspection is disabled
	if report.DoNotInspectCerts {
		return "", "", fmt.Errorf("certificate inspection is disabled")
	}

	fromDecoded, _ := pem.Decode([]byte(from))
	if fromDecoded == nil {
		return "", "", fmt.Errorf("string '%s' is no PEM string", from)
	}

	toDecoded, _ := pem.Decode([]byte(to))
	if toDecoded == nil {
		return "", "", fmt.Errorf("string '%s' is no PEM string", to)
	}

	fromCert, err := x509.ParseCertificate(fromDecoded.Bytes)
	if err != nil {
		return "", "", err
	}

	toCert, err := x509.ParseCertificate(toDecoded.Bytes)
	if err != nil {
		return "", "", err
	}

	return certificateSummaryAsYAML(fromCert),
		certificateSummaryAsYAML(toCert),
		nil
}

// writeTextBlocks writes strings into the provided buffer in either a table style (each string a column) or list style (each string a row)
func (report *JsonReport) writeTextBlocks(buf stringWriter, indent int, blocks ...string) {
	const separator = "   "

	// Calcuclate the theoretical maximum line length if blocks would be rendered next to each other
	theoreticalMaxLineLength := indent + ((len(blocks) - 1) * plainTextLength(separator))
	for _, block := range blocks {
		maxLineLengthInBlock := 0
		for _, line := range strings.Split(block, "\n") {
			if lineLength := plainTextLength(line); maxLineLengthInBlock < lineLength {
				maxLineLengthInBlock = lineLength
			}
		}

		theoreticalMaxLineLength += maxLineLengthInBlock
	}

	// In case the line with blocks next to each other would surpass the terminal width, fall back to the no-table-style
	if report.NoTableStyle || theoreticalMaxLineLength > term.GetTerminalWidth() {
		for _, block := range blocks {
			lines := strings.Split(block, "\n")
			for _, line := range lines {
				_, _ = buf.WriteString(strings.Repeat(" ", indent))
				_, _ = buf.WriteString(line)
				_, _ = buf.WriteString("\n")
			}
		}

	} else {
		_, _ = buf.WriteString(CreateTableStyleString(separator, indent, blocks...))
	}
}

