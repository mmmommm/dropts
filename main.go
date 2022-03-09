package main

import (
	"fmt"
	"os"

	"github.com/mmmommm/dropts/lexer"
	"github.com/mmmommm/dropts/parser"
)

func main() {
	input := os.Args[0]
	token := lexer(input)
	fmt.Printf("lexered: %s\n", token)
	ast, ok := parser.Parse(token)
	if !ok {
		return
	}
	fmt.Printf("parsed: %s\n", ast)
	droppedCode := transform(token)
	fmt.Printf("transformed: %s\n", droppedCode)
}
