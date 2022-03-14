package main

import (
	"fmt"
	"os"

	//"github.com/mmmommm/dropts/parser"
)

func main() {
	input := os.Args[1]

	// ast, ok := parser.Parse(input)
	// if !ok {
	// 	return
	// }
	fmt.Printf("parsed: %s\n", input)
}
