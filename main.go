package main

import (
	"fmt"
	"os"

	"github.com/mmmommm/dropts/v1/parser"
)

func main() {
	input := os.Args[0]
	ast, ok := parser.Parse(input)
	if !ok {
		return
	}
	fmt.Printf("parsed: %s\n", ast)
}
