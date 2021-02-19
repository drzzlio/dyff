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

package cmd

import (
	"github.com/gonvenience/bunt"
	"github.com/gonvenience/term"
	"github.com/gonvenience/ytbx"
	"github.com/spf13/cobra"
)

// ExitCode is just a way to transport the exit code to the main package
type ExitCode struct {
	Value int
}

func (e ExitCode) Error() string {
	return ""
}

// rootCmd represents the base command when called without any subcommands
var rootCmd = &cobra.Command{
	Use:           "dyff",
	SilenceErrors: true,
	SilenceUsage:  true,
	Long: `
δyƒƒ /ˈdʏf/ - a diff tool for YAML files, and sometimes JSON. Also, It
can transform YAML to JSON, and vice versa. The order of keys in hashes
is preserved during the conversion.
`,
}

// ResetSettings resets command settings to default. This is only required by
// the test suite to make sure that the flag parsing works correctly.
func ResetSettings() {
	reportOptions = reportConfig{style: defaultOutputStyle}
	betweenCmdSettings = betweenCmdOptions{}
	yamlCmdSettings = yamlCmdOptions{}
	jsonCmdSettings = jsonCmdOptions{}
}

// Execute adds all child commands to the root command and sets flags appropriately.
// This is called by main.main(). It only needs to happen once to the rootCmd.
func Execute() error {
	return rootCmd.Execute()
}

func init() {
	rootCmd.Flags().SortFlags = false
	rootCmd.PersistentFlags().SortFlags = false

	rootCmd.PersistentFlags().VarP(&bunt.ColorSetting, "color", "c", "specify color usage: on, off, or auto")
	rootCmd.PersistentFlags().VarP(&bunt.TrueColorSetting, "truecolor", "t", "specify true color usage: on, off, or auto")
	rootCmd.PersistentFlags().IntVarP(&term.FixedTerminalWidth, "fixed-width", "w", -1, "disable terminal width detection and use provided fixed value")
	rootCmd.PersistentFlags().BoolVarP(&ytbx.PreserveKeyOrderInJSON, "preserve-key-order-in-json", "k", false, "use ordered keys during JSON decoding (non standard behavior)")
}
