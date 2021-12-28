package main

import (
	// "fmt"
	// "io/ioutil"
	"errors"
	"fmt"
	"io/fs"

	// "math"
	// "math/rand"
	// "os"
	// "regexp"
	// "sort"
	// "strconv"
	// "strings"
	"sync"
	// "sync/atomic"
	// "time"
	// "unicode/utf8"

	// "github.com/mmmommm/dropts/api_helpers"
	// "github.com/mmmommm/dropts/ast"
	// "github.com/mmmommm/dropts/bundler"
	// "github.com/mmmommm/dropts/cache"
	// "github.com/mmmommm/dropts/compat"
	"github.com/mmmommm/dropts/ast"
	"github.com/mmmommm/dropts/config"
	"github.com/mmmommm/dropts/graph"

	// "github.com/mmmommm/dropts/helpers"
	// "github.com/mmmommm/dropts/lexer"
	"github.com/mmmommm/dropts/logger"
	"github.com/mmmommm/dropts/parser"
	// "github.com/mmmommm/dropts/resolver"
)

func compileImpl(input string, option parser.Options) string {
	ast, ok := parser.Parse(input, option)
	if !ok {
		return
	}
}

func Compile(input string, options config.Options) string {
	return compileImpl(input, options)
}

type Location struct {
	File       string
	Namespace  string
	Line       int // 1-based
	Column     int // 0-based, in bytes
	Length     int // in bytes
	LineText   string
	Suggestion string
}

type Message struct {
	PluginName string
	Text       string
	Location   *Location
	Notes      []Note

	// Optional user-specified data that is passed through unmodified. You can
	// use this to stash the original error, for example.
	Detail interface{}
}

type Note struct {
	Text     string
	Location *Location
}

type CompileResult struct {
	Errors   []Message
	Warnings []Message

	Output string
}
