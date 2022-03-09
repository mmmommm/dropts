// This file contains code for parsing TypeScript syntax. The parser just skips
// over type expressions as if they are whitespace and doesn't bother generating
// an AST because nothing uses type information.

package parser

import (
	"fmt"
	"strings"

	"github.com/mmmommm/dropts/compat"
	"github.com/mmmommm/dropts/ast"
	"github.com/mmmommm/dropts/v1/lexer"
)

func (p *parser) skipTypeScriptBinding() {
	switch p.lexer.Token {
	case lexer.TIdentifier, lexer.TThis:
		p.lexer.Next()

	case lexer.TOpenBracket:
		p.lexer.Next()

		// "[, , a]"
		for p.lexer.Token == lexer.TComma {
			p.lexer.Next()
		}

		// "[a, b]"
		for p.lexer.Token != lexer.TCloseBracket {
			p.skipTypeScriptBinding()
			if p.lexer.Token != lexer.TComma {
				break
			}
			p.lexer.Next()
		}

		p.lexer.Expect(lexer.TCloseBracket)

	case lexer.TOpenBrace:
		p.lexer.Next()

		for p.lexer.Token != lexer.TCloseBrace {
			foundIdentifier := false

			switch p.lexer.Token {
			case lexer.TDotDotDot:
				p.lexer.Next()

				if p.lexer.Token != lexer.TIdentifier {
					p.lexer.Unexpected()
				}

				// "{...x}"
				foundIdentifier = true
				p.lexer.Next()

			case lexer.TIdentifier:
				// "{x}"
				// "{x: y}"
				foundIdentifier = true
				p.lexer.Next()

				// "{1: y}"
				// "{'x': y}"
			case lexer.TStringLiteral, lexer.TNumericLiteral:
				p.lexer.Next()

			default:
				if p.lexer.IsIdentifierOrKeyword() {
					// "{if: x}"
					p.lexer.Next()
				} else {
					p.lexer.Unexpected()
				}
			}

			if p.lexer.Token == lexer.TColon || !foundIdentifier {
				p.lexer.Expect(lexer.TColon)
				p.skipTypeScriptBinding()
			}

			if p.lexer.Token != lexer.TComma {
				break
			}
			p.lexer.Next()
		}

		p.lexer.Expect(lexer.TCloseBrace)

	default:
		p.lexer.Unexpected()
	}
}

func (p *parser) skipTypeScriptFnArgs() {
	p.lexer.Expect(lexer.TOpenParen)

	for p.lexer.Token != lexer.TCloseParen {
		// "(...a)"
		if p.lexer.Token == lexer.TDotDotDot {
			p.lexer.Next()
		}

		p.skipTypeScriptBinding()

		// "(a?)"
		if p.lexer.Token == lexer.TQuestion {
			p.lexer.Next()
		}

		// "(a: any)"
		if p.lexer.Token == lexer.TColon {
			p.lexer.Next()
			p.skipTypeScriptType(ast.LLowest)
		}

		// "(a, b)"
		if p.lexer.Token != lexer.TComma {
			break
		}
		p.lexer.Next()
	}

	p.lexer.Expect(lexer.TCloseParen)
}

// This is a spot where the TypeScript grammar is highly ambiguous. Here are
// some cases that are valid:
//
//     let x = (y: any): (() => {}) => { };
//     let x = (y: any): () => {} => { };
//     let x = (y: any): (y) => {} => { };
//     let x = (y: any): (y[]) => {};
//     let x = (y: any): (a | b) => {};
//
// Here are some cases that aren't valid:
//
//     let x = (y: any): (y) => {};
//     let x = (y: any): (y) => {return 0};
//     let x = (y: any): asserts y is (y) => {};
//
func (p *parser) skipTypeScriptParenOrFnType() {
	if p.trySkipTypeScriptArrowArgsWithBacktracking() {
		p.skipTypeScriptReturnType()
	} else {
		p.lexer.Expect(lexer.TOpenParen)
		p.skipTypeScriptType(ast.LLowest)
		p.lexer.Expect(lexer.TCloseParen)
	}
}

func (p *parser) skipTypeScriptReturnType() {
	p.skipTypeScriptTypeWithOpts(ast.LLowest, skipTypeOpts{isReturnType: true})
}

func (p *parser) skipTypeScriptType(level ast.L) {
	p.skipTypeScriptTypeWithOpts(level, skipTypeOpts{})
}

type skipTypeOpts struct {
	isReturnType     bool
	allowTupleLabels bool
}

type tsTypeIdentifierKind uint8

const (
	tsTypeIdentifierNormal tsTypeIdentifierKind = iota
	tsTypeIdentifierUnique
	tsTypeIdentifierAbstract
	tsTypeIdentifierAsserts
	tsTypeIdentifierPrefix
	tsTypeIdentifierPrimitive
)

// Use a map to improve lookup speed
var tsTypeIdentifierMap = map[string]tsTypeIdentifierKind{
	"unique":   tsTypeIdentifierUnique,
	"abstract": tsTypeIdentifierAbstract,
	"asserts":  tsTypeIdentifierAsserts,

	"keyof":    tsTypeIdentifierPrefix,
	"readonly": tsTypeIdentifierPrefix,
	"infer":    tsTypeIdentifierPrefix,

	"any":       tsTypeIdentifierPrimitive,
	"never":     tsTypeIdentifierPrimitive,
	"unknown":   tsTypeIdentifierPrimitive,
	"undefined": tsTypeIdentifierPrimitive,
	"object":    tsTypeIdentifierPrimitive,
	"number":    tsTypeIdentifierPrimitive,
	"string":    tsTypeIdentifierPrimitive,
	"boolean":   tsTypeIdentifierPrimitive,
	"bigint":    tsTypeIdentifierPrimitive,
	"symbol":    tsTypeIdentifierPrimitive,
}

func (p *parser) skipTypeScriptTypeWithOpts(level ast.L, opts skipTypeOpts) {
	for {
		switch p.lexer.Token {
		case lexer.TNumericLiteral, lexer.TBigIntegerLiteral, lexer.TStringLiteral,
			lexer.TNoSubstitutionTemplateLiteral, lexer.TTrue, lexer.TFalse,
			lexer.TNull, lexer.TVoid:
			p.lexer.Next()

		case lexer.TConst:
			r := p.lexer.Range()
			p.lexer.Next()

			// "[const: number]"
			if opts.allowTupleLabels && p.lexer.Token == lexer.TColon {
				p.log.Add(logger.Error, &p.tracker, r, "Unexpected \"const\"")
			}

		case lexer.TThis:
			p.lexer.Next()

			// "function check(): this is boolean"
			if p.lexer.IsContextualKeyword("is") && !p.lexer.HasNewlineBefore {
				p.lexer.Next()
				p.skipTypeScriptType(ast.LLowest)
				return
			}

		case lexer.TMinus:
			// "-123"
			// "-123n"
			p.lexer.Next()
			if p.lexer.Token == lexer.TBigIntegerLiteral {
				p.lexer.Next()
			} else {
				p.lexer.Expect(lexer.TNumericLiteral)
			}

		case lexer.TAmpersand:
		case lexer.TBar:
			// Support things like "type Foo = | A | B" and "type Foo = & A & B"
			p.lexer.Next()
			continue

		case lexer.TImport:
			// "import('fs')"
			p.lexer.Next()

			// "[import: number]"
			if opts.allowTupleLabels && p.lexer.Token == lexer.TColon {
				return
			}

			p.lexer.Expect(lexer.TOpenParen)
			p.lexer.Expect(lexer.TStringLiteral)
			p.lexer.Expect(lexer.TCloseParen)

		case lexer.TNew:
			// "new () => Foo"
			// "new <T>() => Foo<T>"
			p.lexer.Next()

			// "[new: number]"
			if opts.allowTupleLabels && p.lexer.Token == lexer.TColon {
				return
			}

			p.skipTypeScriptTypeParameters()
			p.skipTypeScriptParenOrFnType()

		case lexer.TLessThan:
			// "<T>() => Foo<T>"
			p.skipTypeScriptTypeParameters()
			p.skipTypeScriptParenOrFnType()

		case lexer.TOpenParen:
			// "(number | string)"
			p.skipTypeScriptParenOrFnType()

		case lexer.TIdentifier:
			kind := tsTypeIdentifierMap[p.lexer.Identifier]

			if kind == tsTypeIdentifierPrefix {
				p.lexer.Next()
				p.skipTypeScriptType(ast.LPrefix)
				break
			}

			checkTypeParameters := true

			if kind == tsTypeIdentifierUnique {
				p.lexer.Next()

				// "let foo: unique symbol"
				if p.lexer.IsContextualKeyword("symbol") {
					p.lexer.Next()
					break
				}
			} else if kind == tsTypeIdentifierAbstract {
				p.lexer.Next()

				// "let foo: abstract new () => {}" added in TypeScript 4.2
				if p.lexer.Token == lexer.TNew {
					continue
				}
			} else if kind == tsTypeIdentifierAsserts {
				p.lexer.Next()

				// "function assert(x: boolean): asserts x"
				// "function assert(x: boolean): asserts x is boolean"
				if opts.isReturnType && !p.lexer.HasNewlineBefore && (p.lexer.Token == lexer.TIdentifier || p.lexer.Token == lexer.TThis) {
					p.lexer.Next()
				}
			} else if kind == tsTypeIdentifierPrimitive {
				p.lexer.Next()
				checkTypeParameters = false
			} else {
				p.lexer.Next()
			}

			// "function assert(x: any): x is boolean"
			if p.lexer.IsContextualKeyword("is") && !p.lexer.HasNewlineBefore {
				p.lexer.Next()
				p.skipTypeScriptType(ast.LLowest)
				return
			}

			// "let foo: any \n <number>foo" must not become a single type
			if checkTypeParameters && !p.lexer.HasNewlineBefore {
				p.skipTypeScriptTypeArguments(false /* isInsideJSXElement */)
			}

		case lexer.TTypeof:
			p.lexer.Next()

			// "[typeof: number]"
			if opts.allowTupleLabels && p.lexer.Token == lexer.TColon {
				return
			}

			if p.lexer.Token == lexer.TImport {
				// "typeof import('fs')"
				continue
			} else {
				// "typeof x"
				// "typeof x.y"
				for {
					if !p.lexer.IsIdentifierOrKeyword() {
						p.lexer.Expected(lexer.TIdentifier)
					}
					p.lexer.Next()
					if p.lexer.Token != lexer.TDot {
						break
					}
					p.lexer.Next()
				}
			}

		case lexer.TOpenBracket:
			// "[number, string]"
			// "[first: number, second: string]"
			p.lexer.Next()
			for p.lexer.Token != lexer.TCloseBracket {
				if p.lexer.Token == lexer.TDotDotDot {
					p.lexer.Next()
				}
				p.skipTypeScriptTypeWithOpts(ast.LLowest, skipTypeOpts{allowTupleLabels: true})
				if p.lexer.Token == lexer.TQuestion {
					p.lexer.Next()
				}
				if p.lexer.Token == lexer.TColon {
					p.lexer.Next()
					p.skipTypeScriptType(ast.LLowest)
				}
				if p.lexer.Token != lexer.TComma {
					break
				}
				p.lexer.Next()
			}
			p.lexer.Expect(lexer.TCloseBracket)

		case lexer.TOpenBrace:
			p.skipTypeScriptObjectType()

		case lexer.TTemplateHead:
			// "`${'a' | 'b'}-${'c' | 'd'}`"
			for {
				p.lexer.Next()
				p.skipTypeScriptType(ast.LLowest)
				p.lexer.RescanCloseBraceAsTemplateToken()
				if p.lexer.Token == lexer.TTemplateTail {
					p.lexer.Next()
					break
				}
			}

		default:
			// "[function: number]"
			if opts.allowTupleLabels && p.lexer.IsIdentifierOrKeyword() {
				if p.lexer.Token != lexer.TFunction {
					p.log.Add(logger.Error, &p.tracker, p.lexer.Range(), fmt.Sprintf("Unexpected %q", p.lexer.Raw()))
				}
				p.lexer.Next()
				if p.lexer.Token != lexer.TColon {
					p.lexer.Expect(lexer.TColon)
				}
				return
			}

			p.lexer.Unexpected()
		}
		break
	}

	for {
		switch p.lexer.Token {
		case lexer.TBar:
			if level >= ast.LBitwiseOr {
				return
			}
			p.lexer.Next()
			p.skipTypeScriptType(ast.LBitwiseOr)

		case lexer.TAmpersand:
			if level >= ast.LBitwiseAnd {
				return
			}
			p.lexer.Next()
			p.skipTypeScriptType(ast.LBitwiseAnd)

		case lexer.TExclamation:
			// A postfix "!" is allowed in JSDoc types in TypeScript, which are only
			// present in comments. While it's not valid in a non-comment position,
			// it's still parsed and turned into a soft error by the TypeScript
			// compiler. It turns out parsing this is important for correctness for
			// "as" casts because the "!" token must still be consumed.
			if p.lexer.HasNewlineBefore {
				return
			}
			p.lexer.Next()

		case lexer.TDot:
			p.lexer.Next()
			if !p.lexer.IsIdentifierOrKeyword() {
				p.lexer.Expect(lexer.TIdentifier)
			}
			p.lexer.Next()

			// "{ <A extends B>(): c.d \n <E extends F>(): g.h }" must not become a single type
			if !p.lexer.HasNewlineBefore {
				p.skipTypeScriptTypeArguments(false /* isInsideJSXElement */)
			}

		case lexer.TOpenBracket:
			// "{ ['x']: string \n ['y']: string }" must not become a single type
			if p.lexer.HasNewlineBefore {
				return
			}
			p.lexer.Next()
			if p.lexer.Token != lexer.TCloseBracket {
				p.skipTypeScriptType(ast.LLowest)
			}
			p.lexer.Expect(lexer.TCloseBracket)

		case lexer.TExtends:
			// "{ x: number \n extends: boolean }" must not become a single type
			if p.lexer.HasNewlineBefore || level >= ast.LConditional {
				return
			}
			p.lexer.Next()

			// The type following "extends" is not permitted to be another conditional type
			p.skipTypeScriptType(ast.LConditional)
			p.lexer.Expect(lexer.TQuestion)
			p.skipTypeScriptType(ast.LLowest)
			p.lexer.Expect(lexer.TColon)
			p.skipTypeScriptType(ast.LLowest)

		default:
			return
		}
	}
}

func (p *parser) skipTypeScriptObjectType() {
	p.lexer.Expect(lexer.TOpenBrace)

	for p.lexer.Token != lexer.TCloseBrace {
		// "{ -readonly [K in keyof T]: T[K] }"
		// "{ +readonly [K in keyof T]: T[K] }"
		if p.lexer.Token == lexer.TPlus || p.lexer.Token == lexer.TMinus {
			p.lexer.Next()
		}

		// Skip over modifiers and the property identifier
		foundKey := false
		for p.lexer.IsIdentifierOrKeyword() ||
			p.lexer.Token == lexer.TStringLiteral ||
			p.lexer.Token == lexer.TNumericLiteral {
			p.lexer.Next()
			foundKey = true
		}

		if p.lexer.Token == lexer.TOpenBracket {
			// Index signature or computed property
			p.lexer.Next()
			p.skipTypeScriptType(ast.LLowest)

			// "{ [key: string]: number }"
			// "{ readonly [K in keyof T]: T[K] }"
			if p.lexer.Token == lexer.TColon {
				p.lexer.Next()
				p.skipTypeScriptType(ast.LLowest)
			} else if p.lexer.Token == lexer.TIn {
				p.lexer.Next()
				p.skipTypeScriptType(ast.LLowest)
				if p.lexer.IsContextualKeyword("as") {
					// "{ [K in keyof T as `get-${K}`]: T[K] }"
					p.lexer.Next()
					p.skipTypeScriptType(ast.LLowest)
				}
			}

			p.lexer.Expect(lexer.TCloseBracket)

			// "{ [K in keyof T]+?: T[K] }"
			// "{ [K in keyof T]-?: T[K] }"
			if p.lexer.Token == lexer.TPlus || p.lexer.Token == lexer.TMinus {
				p.lexer.Next()
			}

			foundKey = true
		}

		// "?" indicates an optional property
		// "!" indicates an initialization assertion
		if foundKey && (p.lexer.Token == lexer.TQuestion || p.lexer.Token == lexer.TExclamation) {
			p.lexer.Next()
		}

		// Type parameters come right after the optional mark
		p.skipTypeScriptTypeParameters()

		switch p.lexer.Token {
		case lexer.TColon:
			// Regular property
			if !foundKey {
				p.lexer.Expect(lexer.TIdentifier)
			}
			p.lexer.Next()
			p.skipTypeScriptType(ast.LLowest)

		case lexer.TOpenParen:
			// Method signature
			p.skipTypeScriptFnArgs()
			if p.lexer.Token == lexer.TColon {
				p.lexer.Next()
				p.skipTypeScriptReturnType()
			}

		default:
			if !foundKey {
				p.lexer.Unexpected()
			}
		}

		switch p.lexer.Token {
		case lexer.TCloseBrace:

		case lexer.TComma, lexer.TSemicolon:
			p.lexer.Next()

		default:
			if !p.lexer.HasNewlineBefore {
				p.lexer.Unexpected()
			}
		}
	}

	p.lexer.Expect(lexer.TCloseBrace)
}

// This is the type parameter declarations that go with other symbol
// declarations (class, function, type, etc.)
func (p *parser) skipTypeScriptTypeParameters() {
	if p.lexer.Token == lexer.TLessThan {
		p.lexer.Next()

		for {
			p.lexer.Expect(lexer.TIdentifier)

			// "class Foo<T extends number> {}"
			if p.lexer.Token == lexer.TExtends {
				p.lexer.Next()
				p.skipTypeScriptType(ast.LLowest)
			}

			// "class Foo<T = void> {}"
			if p.lexer.Token == lexer.TEquals {
				p.lexer.Next()
				p.skipTypeScriptType(ast.LLowest)
			}

			if p.lexer.Token != lexer.TComma {
				break
			}
			p.lexer.Next()
			if p.lexer.Token == lexer.TGreaterThan {
				break
			}
		}

		p.lexer.ExpectGreaterThan(false /* isInsideJSXElement */)
	}
}

func (p *parser) skipTypeScriptTypeArguments(isInsideJSXElement bool) bool {
	switch p.lexer.Token {
	case lexer.TLessThan, lexer.TLessThanEquals,
		lexer.TLessThanLessThan, lexer.TLessThanLessThanEquals:
	default:
		return false
	}

	p.lexer.ExpectLessThan(false /* isInsideJSXElement */)

	for {
		p.skipTypeScriptType(ast.LLowest)
		if p.lexer.Token != lexer.TComma {
			break
		}
		p.lexer.Next()
	}

	// This type argument list must end with a ">"
	p.lexer.ExpectGreaterThan(isInsideJSXElement)
	return true
}

func (p *parser) trySkipTypeScriptTypeArgumentsWithBacktracking() bool {
	oldLexer := p.lexer
	p.lexer.IsLogDisabled = true

	// Implement backtracking by restoring the lexer's memory to its original state
	defer func() {
		r := recover()
		if _, isLexerPanic := r.(lexer.LexerPanic); isLexerPanic {
			p.lexer = oldLexer
		} else if r != nil {
			panic(r)
		}
	}()

	p.skipTypeScriptTypeArguments(false /* isInsideJSXElement */)

	// Check the token after this and backtrack if it's the wrong one
	if !p.canFollowTypeArgumentsInExpression() {
		p.lexer.Unexpected()
	}

	// Restore the log disabled flag. Note that we can't just set it back to false
	// because it may have been true to start with.
	p.lexer.IsLogDisabled = oldLexer.IsLogDisabled
	return true
}

func (p *parser) trySkipTypeScriptTypeParametersThenOpenParenWithBacktracking() bool {
	oldLexer := p.lexer
	p.lexer.IsLogDisabled = true

	// Implement backtracking by restoring the lexer's memory to its original state
	defer func() {
		r := recover()
		if _, isLexerPanic := r.(lexer.LexerPanic); isLexerPanic {
			p.lexer = oldLexer
		} else if r != nil {
			panic(r)
		}
	}()

	p.skipTypeScriptTypeParameters()
	if p.lexer.Token != lexer.TOpenParen {
		p.lexer.Unexpected()
	}

	// Restore the log disabled flag. Note that we can't just set it back to false
	// because it may have been true to start with.
	p.lexer.IsLogDisabled = oldLexer.IsLogDisabled
	return true
}

func (p *parser) trySkipTypeScriptArrowReturnTypeWithBacktracking() bool {
	oldLexer := p.lexer
	p.lexer.IsLogDisabled = true

	// Implement backtracking by restoring the lexer's memory to its original state
	defer func() {
		r := recover()
		if _, isLexerPanic := r.(lexer.LexerPanic); isLexerPanic {
			p.lexer = oldLexer
		} else if r != nil {
			panic(r)
		}
	}()

	p.lexer.Expect(lexer.TColon)
	p.skipTypeScriptReturnType()

	// Check the token after this and backtrack if it's the wrong one
	if p.lexer.Token != lexer.TEqualsGreaterThan {
		p.lexer.Unexpected()
	}

	// Restore the log disabled flag. Note that we can't just set it back to false
	// because it may have been true to start with.
	p.lexer.IsLogDisabled = oldLexer.IsLogDisabled
	return true
}

func (p *parser) trySkipTypeScriptArrowArgsWithBacktracking() bool {
	oldLexer := p.lexer
	p.lexer.IsLogDisabled = true

	// Implement backtracking by restoring the lexer's memory to its original state
	defer func() {
		r := recover()
		if _, isLexerPanic := r.(lexer.LexerPanic); isLexerPanic {
			p.lexer = oldLexer
		} else if r != nil {
			panic(r)
		}
	}()

	p.skipTypeScriptFnArgs()
	p.lexer.Expect(lexer.TEqualsGreaterThan)

	// Restore the log disabled flag. Note that we can't just set it back to false
	// because it may have been true to start with.
	p.lexer.IsLogDisabled = oldLexer.IsLogDisabled
	return true
}

// Returns true if the current less-than token is considered to be an arrow
// function under TypeScript's rules for files containing JSX syntax
func (p *parser) isTSArrowFnJSX() (isTSArrowFn bool) {
	oldLexer := p.lexer
	p.lexer.Next()

	// Look ahead to see if this should be an arrow function instead
	if p.lexer.Token == lexer.TIdentifier {
		p.lexer.Next()
		if p.lexer.Token == lexer.TComma {
			isTSArrowFn = true
		} else if p.lexer.Token == lexer.TExtends {
			p.lexer.Next()
			isTSArrowFn = p.lexer.Token != lexer.TEquals && p.lexer.Token != lexer.TGreaterThan
		}
	}

	// Restore the lexer
	p.lexer = oldLexer
	return
}

// This function is taken from the official TypeScript compiler source code:
// https://github.com/microsoft/TypeScript/blob/master/src/compiler/parser.ts
func (p *parser) canFollowTypeArgumentsInExpression() bool {
	switch p.lexer.Token {
	case
		// These are the only tokens can legally follow a type argument list. So we
		// definitely want to treat them as type arg lists.
		lexer.TOpenParen,                     // foo<x>(
		lexer.TNoSubstitutionTemplateLiteral, // foo<T> `...`
		lexer.TTemplateHead:                  // foo<T> `...${100}...`
		return true

	case
		// These cases can't legally follow a type arg list. However, they're not
		// legal expressions either. The user is probably in the middle of a
		// generic type. So treat it as such.
		lexer.TDot,                     // foo<x>.
		lexer.TCloseParen,              // foo<x>)
		lexer.TCloseBracket,            // foo<x>]
		lexer.TColon,                   // foo<x>:
		lexer.TSemicolon,               // foo<x>;
		lexer.TQuestion,                // foo<x>?
		lexer.TEqualsEquals,            // foo<x> ==
		lexer.TEqualsEqualsEquals,      // foo<x> ===
		lexer.TExclamationEquals,       // foo<x> !=
		lexer.TExclamationEqualsEquals, // foo<x> !==
		lexer.TAmpersandAmpersand,      // foo<x> &&
		lexer.TBarBar,                  // foo<x> ||
		lexer.TQuestionQuestion,        // foo<x> ??
		lexer.TCaret,                   // foo<x> ^
		lexer.TAmpersand,               // foo<x> &
		lexer.TBar,                     // foo<x> |
		lexer.TCloseBrace,              // foo<x> }
		lexer.TEndOfFile:               // foo<x>
		return true

	case
		// We don't want to treat these as type arguments. Otherwise we'll parse
		// this as an invocation expression. Instead, we want to parse out the
		// expression in isolation from the type arguments.
		lexer.TComma,     // foo<x>,
		lexer.TOpenBrace: // foo<x> {
		return false

	default:
		// Anything else treat as an expression.
		return false
	}
}

func (p *parser) skipTypeScriptInterfaceStmt(opts parseStmtOpts) {
	name := p.lexer.Identifier
	p.lexer.Expect(lexer.TIdentifier)

	if opts.isModuleScope {
		p.localTypeNames[name] = true
	}

	p.skipTypeScriptTypeParameters()

	if p.lexer.Token == lexer.TExtends {
		p.lexer.Next()
		for {
			p.skipTypeScriptType(ast.LLowest)
			if p.lexer.Token != lexer.TComma {
				break
			}
			p.lexer.Next()
		}
	}

	if p.lexer.IsContextualKeyword("implements") {
		p.lexer.Next()
		for {
			p.skipTypeScriptType(ast.LLowest)
			if p.lexer.Token != lexer.TComma {
				break
			}
			p.lexer.Next()
		}
	}

	p.skipTypeScriptObjectType()
}

func (p *parser) skipTypeScriptTypeStmt(opts parseStmtOpts) {
	if opts.isExport && p.lexer.Token == lexer.TOpenBrace {
		// "export type {foo}"
		// "export type {foo} from 'bar'"
		p.parseExportClause()
		if p.lexer.IsContextualKeyword("from") {
			p.lexer.Next()
			p.parsePath()
		}
		p.lexer.ExpectOrInsertSemicolon()
		return
	}

	name := p.lexer.Identifier
	p.lexer.Expect(lexer.TIdentifier)

	if opts.isModuleScope {
		p.localTypeNames[name] = true
	}

	p.skipTypeScriptTypeParameters()
	p.lexer.Expect(lexer.TEquals)
	p.skipTypeScriptType(ast.LLowest)
	p.lexer.ExpectOrInsertSemicolon()
}

func (p *parser) parseTypeScriptDecorators() []ast.Expr {
	var tsDecorators []ast.Expr
	if p.options.ts.Parse {
		for p.lexer.Token == lexer.TAt {
			p.lexer.Next()

			// Parse a new/call expression with "exprFlagTSDecorator" so we ignore
			// EIndex expressions, since they may be part of a computed property:
			//
			//   class Foo {
			//     @foo ['computed']() {}
			//   }
			//
			// This matches the behavior of the TypeScript compiler.
			tsDecorators = append(tsDecorators, p.parseExprWithFlags(ast.LNew, exprFlagTSDecorator))
		}
	}
	return tsDecorators
}

func (p *parser) parseTypeScriptEnumStmt(loc logger.Loc, opts parseStmtOpts) ast.Stmt {
	p.lexer.Expect(lexer.TEnum)
	nameLoc := p.lexer.Loc()
	nameText := p.lexer.Identifier
	p.lexer.Expect(lexer.TIdentifier)
	name := ast.LocRef{Loc: nameLoc, Ref: ast.InvalidRef}

	// Generate the namespace object
	exportedMembers := p.getOrCreateExportedNamespaceMembers(nameText, opts.isExport)
	tsNamespace := &ast.TSNamespaceScope{
		ExportedMembers: exportedMembers,
		ArgRef:          ast.InvalidRef,
		IsEnumScope:     true,
	}
	enumMemberData := &ast.TSNamespaceMemberNamespace{
		ExportedMembers: exportedMembers,
	}

	// Declare the enum and create the scope
	if !opts.isTypeScriptDeclare {
		name.Ref = p.declareSymbol(ast.SymbolTSEnum, nameLoc, nameText)
		p.pushScopeForParsePass(ast.ScopeEntry, loc)
		p.currentScope.TSNamespace = tsNamespace
		p.refToTSNamespaceMemberData[name.Ref] = enumMemberData
	}

	p.lexer.Expect(lexer.TOpenBrace)
	values := []ast.EnumValue{}

	oldFnOrArrowData := p.fnOrArrowDataParse
	p.fnOrArrowDataParse = fnOrArrowDataParse{
		isThisDisallowed: true,
		needsAsyncLoc:    logger.Loc{Start: -1},
	}

	// Parse the body
	for p.lexer.Token != lexer.TCloseBrace {
		value := ast.EnumValue{
			Loc: p.lexer.Loc(),
			Ref: ast.InvalidRef,
		}

		// Parse the name
		var nameText string
		if p.lexer.Token == lexer.TStringLiteral {
			value.Name = p.lexer.StringLiteral()
			nameText = lexer.UTF16ToString(value.Name)
		} else if p.lexer.IsIdentifierOrKeyword() {
			nameText = p.lexer.Identifier
			value.Name = lexer.StringToUTF16(nameText)
		} else {
			p.lexer.Expect(lexer.TIdentifier)
		}
		p.lexer.Next()

		// Identifiers can be referenced by other values
		if !opts.isTypeScriptDeclare && lexer.IsIdentifierUTF16(value.Name) {
			value.Ref = p.declareSymbol(ast.SymbolOther, value.Loc, lexer.UTF16ToString(value.Name))
		}

		// Parse the initializer
		if p.lexer.Token == lexer.TEquals {
			p.lexer.Next()
			value.ValueOrNil = p.parseExpr(ast.LComma)
		}

		values = append(values, value)

		// Add this enum value as a member of the enum's namespace
		exportedMembers[nameText] = ast.TSNamespaceMember{
			Loc:         value.Loc,
			Data:        &ast.TSNamespaceMemberProperty{},
			IsEnumValue: true,
		}

		if p.lexer.Token != lexer.TComma && p.lexer.Token != lexer.TSemicolon {
			break
		}
		p.lexer.Next()
	}

	p.fnOrArrowDataParse = oldFnOrArrowData

	if !opts.isTypeScriptDeclare {
		// Avoid a collision with the enum closure argument variable if the
		// enum exports a symbol with the same name as the enum itself:
		//
		//   enum foo {
		//     foo = 123,
		//     bar = foo,
		//   }
		//
		// TypeScript generates the following code in this case:
		//
		//   var foo;
		//   (function (foo) {
		//     foo[foo["foo"] = 123] = "foo";
		//     foo[foo["bar"] = 123] = "bar";
		//   })(foo || (foo = {}));
		//
		// Whereas in this case:
		//
		//   enum foo {
		//     bar = foo as any,
		//   }
		//
		// TypeScript generates the following code:
		//
		//   var foo;
		//   (function (foo) {
		//     foo[foo["bar"] = foo] = "bar";
		//   })(foo || (foo = {}));
		//
		if _, ok := p.currentScope.Members[nameText]; ok {
			// Add a "_" to make tests easier to read, since non-bundler tests don't
			// run the renamer. For external-facing things the renamer will avoid
			// collisions automatically so this isn't important for correctness.
			tsNamespace.ArgRef = p.newSymbol(ast.SymbolHoisted, "_"+nameText)
			p.currentScope.Generated = append(p.currentScope.Generated, tsNamespace.ArgRef)
		} else {
			tsNamespace.ArgRef = p.declareSymbol(ast.SymbolHoisted, nameLoc, nameText)
		}
		p.refToTSNamespaceMemberData[tsNamespace.ArgRef] = enumMemberData

		p.popScope()
	}

	p.lexer.Expect(lexer.TCloseBrace)

	if opts.isTypeScriptDeclare {
		if opts.isNamespaceScope && opts.isExport {
			p.hasNonLocalExportDeclareInsideNamespace = true
		}

		return ast.Stmt{Loc: loc, Data: &ast.STypeScript{}}
	}

	return ast.Stmt{Loc: loc, Data: &ast.SEnum{
		Name:     name,
		Arg:      tsNamespace.ArgRef,
		Values:   values,
		IsExport: opts.isExport,
	}}
}

// This assumes the caller has already parsed the "import" token
func (p *parser) parseTypeScriptImportEqualsStmt(loc logger.Loc, opts parseStmtOpts, defaultNameLoc logger.Loc, defaultName string) ast.Stmt {
	p.lexer.Expect(lexer.TEquals)

	kind := p.selectLocalKind(ast.LocalConst)
	name := p.lexer.Identifier
	value := ast.Expr{Loc: p.lexer.Loc(), Data: &ast.EIdentifier{Ref: p.storeNameInRef(name)}}
	p.lexer.Expect(lexer.TIdentifier)

	if name == "require" && p.lexer.Token == lexer.TOpenParen {
		// "import ns = require('x')"
		p.lexer.Next()
		path := ast.Expr{Loc: p.lexer.Loc(), Data: &ast.EString{Value: p.lexer.StringLiteral()}}
		p.lexer.Expect(lexer.TStringLiteral)
		p.lexer.Expect(lexer.TCloseParen)
		value.Data = &ast.ECall{
			Target: value,
			Args:   []ast.Expr{path},
		}
	} else {
		// "import Foo = Bar"
		// "import Foo = Bar.Baz"
		for p.lexer.Token == lexer.TDot {
			p.lexer.Next()
			value.Data = &ast.EDot{
				Target:  value,
				Name:    p.lexer.Identifier,
				NameLoc: p.lexer.Loc(),
			}
			p.lexer.Expect(lexer.TIdentifier)
		}
	}

	p.lexer.ExpectOrInsertSemicolon()

	if opts.isTypeScriptDeclare {
		// "import type foo = require('bar');"
		// "import type foo = bar.baz;"
		return ast.Stmt{Loc: loc, Data: &ast.STypeScript{}}
	}

	ref := p.declareSymbol(ast.SymbolConst, defaultNameLoc, defaultName)
	decls := []ast.Decl{{
		Binding:    ast.Binding{Loc: defaultNameLoc, Data: &ast.BIdentifier{Ref: ref}},
		ValueOrNil: value,
	}}

	return ast.Stmt{Loc: loc, Data: &ast.SLocal{
		Kind:              kind,
		Decls:             decls,
		IsExport:          opts.isExport,
		WasTSImportEquals: true,
	}}
}

// Generate a TypeScript namespace object for this namespace's scope. If this
// namespace is another block that is to be merged with an existing namespace,
// use that earlier namespace's object instead.
func (p *parser) getOrCreateExportedNamespaceMembers(name string, isExport bool) ast.TSNamespaceMembers {
	// Merge with a sibling namespace from the same scope
	if existingMember, ok := p.currentScope.Members[name]; ok {
		if memberData, ok := p.refToTSNamespaceMemberData[existingMember.Ref]; ok {
			if nsMemberData, ok := memberData.(*ast.TSNamespaceMemberNamespace); ok {
				return nsMemberData.ExportedMembers
			}
		}
	}

	// Merge with a sibling namespace from a different scope
	if isExport {
		if parentNamespace := p.currentScope.TSNamespace; parentNamespace != nil {
			if existing, ok := parentNamespace.ExportedMembers[name]; ok {
				if existing, ok := existing.Data.(*ast.TSNamespaceMemberNamespace); ok {
					return existing.ExportedMembers
				}
			}
		}
	}

	// Otherwise, generate a new namespace object
	return make(ast.TSNamespaceMembers)
}

func (p *parser) parseTypeScriptNamespaceStmt(loc logger.Loc, opts parseStmtOpts) ast.Stmt {
	// "namespace Foo {}"
	nameLoc := p.lexer.Loc()
	nameText := p.lexer.Identifier
	p.lexer.Next()

	// Generate the namespace object
	exportedMembers := p.getOrCreateExportedNamespaceMembers(nameText, opts.isExport)
	tsNamespace := &ast.TSNamespaceScope{
		ExportedMembers: exportedMembers,
		ArgRef:          ast.InvalidRef,
	}
	nsMemberData := &ast.TSNamespaceMemberNamespace{
		ExportedMembers: exportedMembers,
	}

	// Declare the namespace and create the scope
	name := ast.LocRef{Loc: nameLoc, Ref: ast.InvalidRef}
	scopeIndex := p.pushScopeForParsePass(ast.ScopeEntry, loc)
	p.currentScope.TSNamespace = tsNamespace

	oldHasNonLocalExportDeclareInsideNamespace := p.hasNonLocalExportDeclareInsideNamespace
	oldFnOrArrowData := p.fnOrArrowDataParse
	p.hasNonLocalExportDeclareInsideNamespace = false
	p.fnOrArrowDataParse = fnOrArrowDataParse{
		isThisDisallowed:   true,
		isReturnDisallowed: true,
		needsAsyncLoc:      logger.Loc{Start: -1},
	}

	// Parse the statements inside the namespace
	var stmts []ast.Stmt
	if p.lexer.Token == lexer.TDot {
		dotLoc := p.lexer.Loc()
		p.lexer.Next()
		stmts = []ast.Stmt{p.parseTypeScriptNamespaceStmt(dotLoc, parseStmtOpts{
			isExport:            true,
			isNamespaceScope:    true,
			isTypeScriptDeclare: opts.isTypeScriptDeclare,
		})}
	} else if opts.isTypeScriptDeclare && p.lexer.Token != lexer.TOpenBrace {
		p.lexer.ExpectOrInsertSemicolon()
	} else {
		p.lexer.Expect(lexer.TOpenBrace)
		stmts = p.parseStmtsUpTo(lexer.TCloseBrace, parseStmtOpts{
			isNamespaceScope:    true,
			isTypeScriptDeclare: opts.isTypeScriptDeclare,
		})
		p.lexer.Next()
	}

	hasNonLocalExportDeclareInsideNamespace := p.hasNonLocalExportDeclareInsideNamespace
	p.hasNonLocalExportDeclareInsideNamespace = oldHasNonLocalExportDeclareInsideNamespace
	p.fnOrArrowDataParse = oldFnOrArrowData

	// Add any exported members from this namespace's body as members of the
	// associated namespace object.
	for _, stmt := range stmts {
		switch s := stmt.Data.(type) {
		case *ast.SFunction:
			if s.IsExport {
				name := p.symbols[s.Fn.Name.Ref.InnerIndex].OriginalName
				member := ast.TSNamespaceMember{
					Loc:  s.Fn.Name.Loc,
					Data: &ast.TSNamespaceMemberProperty{},
				}
				exportedMembers[name] = member
				p.refToTSNamespaceMemberData[s.Fn.Name.Ref] = member.Data
			}

		case *ast.SClass:
			if s.IsExport {
				name := p.symbols[s.Class.Name.Ref.InnerIndex].OriginalName
				member := ast.TSNamespaceMember{
					Loc:  s.Class.Name.Loc,
					Data: &ast.TSNamespaceMemberProperty{},
				}
				exportedMembers[name] = member
				p.refToTSNamespaceMemberData[s.Class.Name.Ref] = member.Data
			}

		case *ast.SNamespace:
			if s.IsExport {
				if memberData, ok := p.refToTSNamespaceMemberData[s.Name.Ref]; ok {
					if nsMemberData, ok := memberData.(*ast.TSNamespaceMemberNamespace); ok {
						member := ast.TSNamespaceMember{
							Loc: s.Name.Loc,
							Data: &ast.TSNamespaceMemberNamespace{
								ExportedMembers: nsMemberData.ExportedMembers,
							},
						}
						exportedMembers[p.symbols[s.Name.Ref.InnerIndex].OriginalName] = member
						p.refToTSNamespaceMemberData[s.Name.Ref] = member.Data
					}
				}
			}

		case *ast.SEnum:
			if s.IsExport {
				if memberData, ok := p.refToTSNamespaceMemberData[s.Name.Ref]; ok {
					if nsMemberData, ok := memberData.(*ast.TSNamespaceMemberNamespace); ok {
						member := ast.TSNamespaceMember{
							Loc: s.Name.Loc,
							Data: &ast.TSNamespaceMemberNamespace{
								ExportedMembers: nsMemberData.ExportedMembers,
							},
						}
						exportedMembers[p.symbols[s.Name.Ref.InnerIndex].OriginalName] = member
						p.refToTSNamespaceMemberData[s.Name.Ref] = member.Data
					}
				}
			}

		case *ast.SLocal:
			if s.IsExport {
				p.exportDeclsInsideNamespace(exportedMembers, s.Decls)
			}
		}
	}

	// Import assignments may be only used in type expressions, not value
	// expressions. If this is the case, the TypeScript compiler removes
	// them entirely from the output. That can cause the namespace itself
	// to be considered empty and thus be removed.
	importEqualsCount := 0
	for _, stmt := range stmts {
		if local, ok := stmt.Data.(*ast.SLocal); ok && local.WasTSImportEquals && !local.IsExport {
			importEqualsCount++
		}
	}

	// TypeScript omits namespaces without values. These namespaces
	// are only allowed to be used in type expressions. They are
	// allowed to be exported, but can also only be used in type
	// expressions when imported. So we shouldn't count them as a
	// real export either.
	//
	// TypeScript also strangely counts namespaces containing only
	// "export declare" statements as non-empty even though "declare"
	// statements are only type annotations. We cannot omit the namespace
	// in that case. See https://github.com/evanw/esbuild/issues/1158.
	if (len(stmts) == importEqualsCount && !hasNonLocalExportDeclareInsideNamespace) || opts.isTypeScriptDeclare {
		p.popAndDiscardScope(scopeIndex)
		if opts.isModuleScope {
			p.localTypeNames[nameText] = true
		}
		return ast.Stmt{Loc: loc, Data: &ast.STypeScript{}}
	}

	if !opts.isTypeScriptDeclare {
		// Avoid a collision with the namespace closure argument variable if the
		// namespace exports a symbol with the same name as the namespace itself:
		//
		//   namespace foo {
		//     export let foo = 123
		//     console.log(foo)
		//   }
		//
		// TypeScript generates the following code in this case:
		//
		//   var foo;
		//   (function (foo_1) {
		//     foo_1.foo = 123;
		//     console.log(foo_1.foo);
		//   })(foo || (foo = {}));
		//
		if _, ok := p.currentScope.Members[nameText]; ok {
			// Add a "_" to make tests easier to read, since non-bundler tests don't
			// run the renamer. For external-facing things the renamer will avoid
			// collisions automatically so this isn't important for correctness.
			tsNamespace.ArgRef = p.newSymbol(ast.SymbolHoisted, "_"+nameText)
			p.currentScope.Generated = append(p.currentScope.Generated, tsNamespace.ArgRef)
		} else {
			tsNamespace.ArgRef = p.declareSymbol(ast.SymbolHoisted, nameLoc, nameText)
		}
		p.refToTSNamespaceMemberData[tsNamespace.ArgRef] = nsMemberData
	}

	p.popScope()
	if !opts.isTypeScriptDeclare {
		name.Ref = p.declareSymbol(ast.SymbolTSNamespace, nameLoc, nameText)
		p.refToTSNamespaceMemberData[name.Ref] = nsMemberData
	}
	return ast.Stmt{Loc: loc, Data: &ast.SNamespace{
		Name:     name,
		Arg:      tsNamespace.ArgRef,
		Stmts:    stmts,
		IsExport: opts.isExport,
	}}
}

func (p *parser) exportDeclsInsideNamespace(exportedMembers ast.TSNamespaceMembers, decls []ast.Decl) {
	for _, decl := range decls {
		p.exportBindingInsideNamespace(exportedMembers, decl.Binding)
	}
}

func (p *parser) exportBindingInsideNamespace(exportedMembers ast.TSNamespaceMembers, binding ast.Binding) {
	switch b := binding.Data.(type) {
	case *ast.BMissing:

	case *ast.BIdentifier:
		name := p.symbols[b.Ref.InnerIndex].OriginalName
		member := ast.TSNamespaceMember{
			Loc:  binding.Loc,
			Data: &ast.TSNamespaceMemberProperty{},
		}
		exportedMembers[name] = member
		p.refToTSNamespaceMemberData[b.Ref] = member.Data

	case *ast.BArray:
		for _, item := range b.Items {
			p.exportBindingInsideNamespace(exportedMembers, item.Binding)
		}

	case *ast.BObject:
		for _, property := range b.Properties {
			p.exportBindingInsideNamespace(exportedMembers, property.Value)
		}

	default:
		panic("Internal error")
	}
}

func (p *parser) generateClosureForTypeScriptNamespaceOrEnum(
	stmts []ast.Stmt, stmtLoc logger.Loc, isExport bool, nameLoc logger.Loc,
	nameRef ast.Ref, argRef ast.Ref, stmtsInsideClosure []ast.Stmt,
) []ast.Stmt {
	// Follow the link chain in case symbols were merged
	symbol := p.symbols[nameRef.InnerIndex]
	for symbol.Link != ast.InvalidRef {
		nameRef = symbol.Link
		symbol = p.symbols[nameRef.InnerIndex]
	}

	// Make sure to only emit a variable once for a given namespace, since there
	// can be multiple namespace blocks for the same namespace
	if (symbol.Kind == ast.SymbolTSNamespace || symbol.Kind == ast.SymbolTSEnum) && !p.emittedNamespaceVars[nameRef] {
		decls := []ast.Decl{{Binding: ast.Binding{Loc: nameLoc, Data: &ast.BIdentifier{Ref: nameRef}}}}
		p.emittedNamespaceVars[nameRef] = true
		if p.currentScope == p.moduleScope {
			// Top-level namespace: "var"
			stmts = append(stmts, ast.Stmt{Loc: stmtLoc, Data: &ast.SLocal{
				Kind:     ast.LocalVar,
				Decls:    decls,
				IsExport: isExport,
			}})
		} else {
			// Nested namespace: "let"
			stmts = append(stmts, ast.Stmt{Loc: stmtLoc, Data: &ast.SLocal{
				Kind:  ast.LocalLet,
				Decls: decls,
			}})
		}
	}

	var argExpr ast.Expr
	if isExport && p.enclosingNamespaceArgRef != nil {
		// "name = enclosing.name || (enclosing.name = {})"
		name := p.symbols[nameRef.InnerIndex].OriginalName
		argExpr = ast.Assign(
			ast.Expr{Loc: nameLoc, Data: &ast.EIdentifier{Ref: nameRef}},
			ast.Expr{Loc: nameLoc, Data: &ast.EBinary{
				Op: ast.BinOpLogicalOr,
				Left: ast.Expr{Loc: nameLoc, Data: &ast.EDot{
					Target:  ast.Expr{Loc: nameLoc, Data: &ast.EIdentifier{Ref: *p.enclosingNamespaceArgRef}},
					Name:    name,
					NameLoc: nameLoc,
				}},
				Right: ast.Assign(
					ast.Expr{Loc: nameLoc, Data: &ast.EDot{
						Target:  ast.Expr{Loc: nameLoc, Data: &ast.EIdentifier{Ref: *p.enclosingNamespaceArgRef}},
						Name:    name,
						NameLoc: nameLoc,
					}},
					ast.Expr{Loc: nameLoc, Data: &ast.EObject{}},
				),
			}},
		)
		p.recordUsage(*p.enclosingNamespaceArgRef)
		p.recordUsage(*p.enclosingNamespaceArgRef)
		p.recordUsage(nameRef)
	} else {
		// "name || (name = {})"
		argExpr = ast.Expr{Loc: nameLoc, Data: &ast.EBinary{
			Op:   ast.BinOpLogicalOr,
			Left: ast.Expr{Loc: nameLoc, Data: &ast.EIdentifier{Ref: nameRef}},
			Right: ast.Assign(
				ast.Expr{Loc: nameLoc, Data: &ast.EIdentifier{Ref: nameRef}},
				ast.Expr{Loc: nameLoc, Data: &ast.EObject{}},
			),
		}}
		p.recordUsage(nameRef)
		p.recordUsage(nameRef)
	}

	// Try to use an arrow function if possible for compactness
	var targetExpr ast.Expr
	args := []ast.Arg{{Binding: ast.Binding{Loc: nameLoc, Data: &ast.BIdentifier{Ref: argRef}}}}
	if p.options.unsupportedJSFeatures.Has(compat.Arrow) {
		targetExpr = ast.Expr{Loc: stmtLoc, Data: &ast.EFunction{Fn: ast.Fn{
			Args: args,
			Body: ast.FnBody{Loc: stmtLoc, Stmts: stmtsInsideClosure},
		}}}
	} else {
		targetExpr = ast.Expr{Loc: stmtLoc, Data: &ast.EArrow{
			Args: args,
			Body: ast.FnBody{Loc: stmtLoc, Stmts: stmtsInsideClosure},
		}}
	}

	// Call the closure with the name object
	stmts = append(stmts, ast.Stmt{Loc: stmtLoc, Data: &ast.SExpr{Value: ast.Expr{Loc: stmtLoc, Data: &ast.ECall{
		Target: targetExpr,
		Args:   []ast.Expr{argExpr},
	}}}})

	return stmts
}

func (p *parser) generateClosureForTypeScriptEnum(
	stmts []ast.Stmt, stmtLoc logger.Loc, isExport bool, nameLoc logger.Loc,
	nameRef ast.Ref, argRef ast.Ref, exprsInsideClosure []ast.Expr,
	allValuesArePure bool,
) []ast.Stmt {
	// Bail back to the namespace code for enums that aren't at the top level.
	// Doing this for nested enums is problematic for two reasons. First of all
	// enums inside of namespaces must be property accesses off the namespace
	// object instead of variable declarations. Also we'd need to use "let"
	// instead of "var" which doesn't allow sibling declarations to be merged.
	if p.currentScope != p.moduleScope {
		stmtsInsideClosure := []ast.Stmt{}
		if len(exprsInsideClosure) > 0 {
			if p.options.mangleSyntax {
				// "a; b; c;" => "a, b, c;"
				joined := ast.JoinAllWithComma(exprsInsideClosure)
				stmtsInsideClosure = append(stmtsInsideClosure, ast.Stmt{Loc: joined.Loc, Data: &ast.SExpr{Value: joined}})
			} else {
				for _, expr := range exprsInsideClosure {
					stmtsInsideClosure = append(stmtsInsideClosure, ast.Stmt{Loc: expr.Loc, Data: &ast.SExpr{Value: expr}})
				}
			}
		}
		return p.generateClosureForTypeScriptNamespaceOrEnum(
			stmts, stmtLoc, isExport, nameLoc, nameRef, argRef, stmtsInsideClosure)
	}

	// This uses an output format for enums that's different but equivalent to
	// what TypeScript uses. Here is TypeScript's output:
	//
	//   var x;
	//   (function (x) {
	//     x[x["y"] = 1] = "y";
	//   })(x || (x = {}));
	//
	// And here's our output:
	//
	//   var x = /* @__PURE__ */ ((x) => {
	//     x[x["y"] = 1] = "y";
	//     return x;
	//   })(x || {});
	//
	// One benefit is that the minified output is smaller:
	//
	//   // Old output minified
	//   var x;(function(n){n[n.y=1]="y"})(x||(x={}));
	//
	//   // New output minified
	//   var x=(r=>(r[r.y=1]="y",r))(x||{});
	//
	// Another benefit is that the @__PURE__ annotation means it automatically
	// works with tree-shaking, even with more advanced features such as sibling
	// enum declarations and enum/namespace merges. Ideally all uses of the enum
	// are just direct references to enum members (and are therefore inlined as
	// long as the enum value is a constant) and the enum definition itself is
	// unused and can be removed as dead code.

	// Follow the link chain in case symbols were merged
	symbol := p.symbols[nameRef.InnerIndex]
	for symbol.Link != ast.InvalidRef {
		nameRef = symbol.Link
		symbol = p.symbols[nameRef.InnerIndex]
	}

	// Generate the body of the closure, including a return statement at the end
	stmtsInsideClosure := []ast.Stmt{}
	if len(exprsInsideClosure) > 0 {
		argExpr := ast.Expr{Loc: nameLoc, Data: &ast.EIdentifier{Ref: argRef}}
		if p.options.mangleSyntax {
			// "a; b; return c;" => "return a, b, c;"
			joined := ast.JoinAllWithComma(exprsInsideClosure)
			joined = ast.JoinWithComma(joined, argExpr)
			stmtsInsideClosure = append(stmtsInsideClosure, ast.Stmt{Loc: joined.Loc, Data: &ast.SReturn{ValueOrNil: joined}})
		} else {
			for _, expr := range exprsInsideClosure {
				stmtsInsideClosure = append(stmtsInsideClosure, ast.Stmt{Loc: expr.Loc, Data: &ast.SExpr{Value: expr}})
			}
			stmtsInsideClosure = append(stmtsInsideClosure, ast.Stmt{Loc: argExpr.Loc, Data: &ast.SReturn{ValueOrNil: argExpr}})
		}
	}

	// Try to use an arrow function if possible for compactness
	var targetExpr ast.Expr
	args := []ast.Arg{{Binding: ast.Binding{Loc: nameLoc, Data: &ast.BIdentifier{Ref: argRef}}}}
	if p.options.unsupportedJSFeatures.Has(compat.Arrow) {
		targetExpr = ast.Expr{Loc: stmtLoc, Data: &ast.EFunction{Fn: ast.Fn{
			Args: args,
			Body: ast.FnBody{Loc: stmtLoc, Stmts: stmtsInsideClosure},
		}}}
	} else {
		targetExpr = ast.Expr{Loc: stmtLoc, Data: &ast.EArrow{
			Args:       args,
			Body:       ast.FnBody{Loc: stmtLoc, Stmts: stmtsInsideClosure},
			PreferExpr: p.options.mangleSyntax,
		}}
	}

	// Call the closure with the name object and store it to the variable
	decls := []ast.Decl{{
		Binding: ast.Binding{Loc: nameLoc, Data: &ast.BIdentifier{Ref: nameRef}},
		ValueOrNil: ast.Expr{Loc: stmtLoc, Data: &ast.ECall{
			Target: targetExpr,
			Args: []ast.Expr{{Loc: nameLoc, Data: &ast.EBinary{
				Op:    ast.BinOpLogicalOr,
				Left:  ast.Expr{Loc: nameLoc, Data: &ast.EIdentifier{Ref: nameRef}},
				Right: ast.Expr{Loc: nameLoc, Data: &ast.EObject{}},
			}}},
			CanBeUnwrappedIfUnused: allValuesArePure,
		}},
	}}
	p.recordUsage(nameRef)

	// Use a "var" statement since this is a top-level enum, but only use "export" once
	stmts = append(stmts, ast.Stmt{Loc: stmtLoc, Data: &ast.SLocal{
		Kind:     ast.LocalVar,
		Decls:    decls,
		IsExport: isExport && !p.emittedNamespaceVars[nameRef],
	}})
	p.emittedNamespaceVars[nameRef] = true

	return stmts
}

func (p *parser) wrapInlinedEnum(value ast.Expr, comment string) ast.Expr {
	if p.shouldFoldNumericConstants || p.options.mangleSyntax || strings.Contains(comment, "*/") {
		// Don't wrap with a comment
		return value
	}

	// Wrap with a comment
	return ast.Expr{Loc: value.Loc, Data: &ast.EInlinedEnum{
		Value:   value,
		Comment: comment,
	}}
}
