// This file contains code for "lowering" syntax, which means converting it to
// older JavaScript. For example, "a ** b" becomes a call to "Math.pow(a, b)"
// when lowered. Which syntax is lowered is determined by the language target.

package parser

import (
	"fmt"

	"github.com/mmmommm/dropts/compat"
	"github.com/mmmommm/dropts/config"
	"github.com/mmmommm/dropts/ast"
	"github.com/mmmommm/dropts/lexer"
	"github.com/mmmommm/dropts/logger"
)

func (p *parser) prettyPrintTargetEnvironment(feature compat.JSFeature) (where string, notes []logger.MsgData) {
	where = "the configured target environment"
	if tsTarget := p.options.tsTarget; tsTarget != nil && tsTarget.UnsupportedJSFeatures.Has(feature) {
		tracker := logger.MakeLineColumnTracker(&tsTarget.Source)
		where = fmt.Sprintf("%s (%q)", where, tsTarget.Target)
		notes = []logger.MsgData{tracker.MsgData(tsTarget.Range, fmt.Sprintf(
			"The target environment was set to %q here:", tsTarget.Target))}
	} else if p.options.originalTargetEnv != "" {
		where = fmt.Sprintf("%s (%s)", where, p.options.originalTargetEnv)
	}
	return
}

func (p *parser) markSyntaxFeature(feature compat.JSFeature, r logger.Range) (didGenerateError bool) {
	didGenerateError = true

	if !p.options.unsupportedJSFeatures.Has(feature) {
		if feature == compat.TopLevelAwait && !p.options.outputFormat.KeepES6ImportExportSyntax() {
			p.log.Add(logger.Error, &p.tracker, r, fmt.Sprintf(
				"Top-level await is currently not supported with the %q output format", p.options.outputFormat.String()))
			return
		}

		didGenerateError = false
		return
	}

	var name string
	where, notes := p.prettyPrintTargetEnvironment(feature)

	switch feature {
	case compat.DefaultArgument:
		name = "default arguments"

	case compat.RestArgument:
		name = "rest arguments"

	case compat.ArraySpread:
		name = "array spread"

	case compat.ForOf:
		name = "for-of loops"

	case compat.ObjectAccessors:
		name = "object accessors"

	case compat.ObjectExtensions:
		name = "object literal extensions"

	case compat.Destructuring:
		name = "destructuring"

	case compat.NewTarget:
		name = "new.target"

	case compat.Const:
		name = "const"

	case compat.Let:
		name = "let"

	case compat.Class:
		name = "class syntax"

	case compat.Generator:
		name = "generator functions"

	case compat.AsyncAwait:
		name = "async functions"

	case compat.AsyncGenerator:
		name = "async generator functions"

	case compat.ForAwait:
		name = "for-await loops"

	case compat.NestedRestBinding:
		name = "non-identifier array rest patterns"

	case compat.ImportAssertions:
		p.log.AddWithNotes(logger.Error, &p.tracker, r, fmt.Sprintf(
			"Using an arbitrary value as the second argument to \"import()\" is not possible in %s", where), notes)
		return

	case compat.TopLevelAwait:
		p.log.AddWithNotes(logger.Error, &p.tracker, r, fmt.Sprintf(
			"Top-level await is not available in %s", where), notes)
		return

	case compat.ArbitraryModuleNamespaceNames:
		p.log.AddWithNotes(logger.Error, &p.tracker, r, fmt.Sprintf(
			"Using a string as a module namespace identifier name is not supported in %s", where), notes)
		return

	case compat.BigInt:
		// Transforming these will never be supported
		p.log.AddWithNotes(logger.Error, &p.tracker, r, fmt.Sprintf(
			"Big integer literals are not available in %s", where), notes)
		return

	case compat.ImportMeta:
		// This can't be polyfilled
		p.log.AddWithNotes(logger.Warning, &p.tracker, r, fmt.Sprintf(
			"\"import.meta\" is not available in %s and will be empty", where), notes)
		return

	default:
		p.log.AddWithNotes(logger.Error, &p.tracker, r, fmt.Sprintf(
			"This feature is not available in %s", where), notes)
		return
	}

	p.log.AddWithNotes(logger.Error, &p.tracker, r, fmt.Sprintf(
		"Transforming %s to %s is not supported yet", name, where), notes)
	return
}

func (p *parser) isStrictMode() bool {
	return p.currentScope.StrictMode != ast.SloppyMode
}

func (p *parser) isStrictModeOutputFormat() bool {
	return p.options.outputFormat == config.FormatESModule
}

type strictModeFeature uint8

const (
	withStatement strictModeFeature = iota
	deleteBareName
	forInVarInit
	evalOrArguments
	reservedWord
	legacyOctalLiteral
	legacyOctalEscape
	ifElseFunctionStmt
	labelFunctionStmt
)

func (p *parser) markStrictModeFeature(feature strictModeFeature, r logger.Range, detail string) {
	var text string
	canBeTransformed := false
	switch feature {
	case withStatement:
		text = "With statements"
	case deleteBareName:
		text = "Delete of a bare identifier"
	case forInVarInit:
		text = "Variable initializers inside for-in loops"
		canBeTransformed = true
	case evalOrArguments:
		text = fmt.Sprintf("Declarations with the name %q", detail)
	case reservedWord:
		text = fmt.Sprintf("%q is a reserved word and", detail)
	case legacyOctalLiteral:
		text = "Legacy octal literals"
	case legacyOctalEscape:
		text = "Legacy octal escape sequences"
	case ifElseFunctionStmt:
		text = "Function declarations inside if statements"
	case labelFunctionStmt:
		text = "Function declarations inside labels"
	default:
		text = "This feature"
	}
	if p.isStrictMode() {
		var why string
		var notes []logger.MsgData
		var where logger.Range
		switch p.currentScope.StrictMode {
		case ast.ImplicitStrictModeImport:
			where = p.es6ImportKeyword
		case ast.ImplicitStrictModeExport:
			where = p.es6ExportKeyword
		case ast.ImplicitStrictModeTopLevelAwait:
			where = p.topLevelAwaitKeyword
		case ast.ImplicitStrictModeClass:
			why = "All code inside a class is implicitly in strict mode"
			where = p.enclosingClassKeyword
		case ast.ExplicitStrictMode:
			why = "Strict mode is triggered by the \"use strict\" directive here:"
			where = p.source.RangeOfString(p.currentScope.UseStrictLoc)
		}
		if where.Len > 0 {
			if why == "" {
				why = fmt.Sprintf("This file is implicitly in strict mode because of the %q keyword here:", p.source.TextForRange(where))
			}
			notes = []logger.MsgData{p.tracker.MsgData(where, why)}
		}
		p.log.AddWithNotes(logger.Error, &p.tracker, r,
			fmt.Sprintf("%s cannot be used in strict mode", text), notes)
	} else if !canBeTransformed && p.isStrictModeOutputFormat() {
		p.log.Add(logger.Error, &p.tracker, r,
			fmt.Sprintf("%s cannot be used with the \"esm\" output format due to strict mode", text))
	}
}

// Mark the feature if "loweredFeature" is unsupported. This is used when one
// feature is implemented in terms of another feature.
func (p *parser) markLoweredSyntaxFeature(feature compat.JSFeature, r logger.Range, loweredFeature compat.JSFeature) {
	if p.options.unsupportedJSFeatures.Has(loweredFeature) {
		p.markSyntaxFeature(feature, r)
	}
}

func (p *parser) privateSymbolNeedsToBeLowered(private *ast.EPrivateIdentifier) bool {
	symbol := &p.symbols[private.Ref.InnerIndex]
	return p.options.unsupportedJSFeatures.Has(symbol.Kind.Feature()) || symbol.PrivateSymbolMustBeLowered
}

func (p *parser) captureThis() ast.Ref {
	if p.fnOnlyDataVisit.thisCaptureRef == nil {
		ref := p.newSymbol(ast.SymbolHoisted, "_this")
		p.fnOnlyDataVisit.thisCaptureRef = &ref
	}
	return *p.fnOnlyDataVisit.thisCaptureRef
}

func (p *parser) captureArguments() ast.Ref {
	if p.fnOnlyDataVisit.argumentsCaptureRef == nil {
		ref := p.newSymbol(ast.SymbolHoisted, "_arguments")
		p.fnOnlyDataVisit.argumentsCaptureRef = &ref
	}
	return *p.fnOnlyDataVisit.argumentsCaptureRef
}

func (p *parser) lowerFunction(
	isAsync *bool,
	args *[]ast.Arg,
	bodyLoc logger.Loc,
	bodyStmts *[]ast.Stmt,
	preferExpr *bool,
	hasRestArg *bool,
	isArrow bool,
	superHelpers *superHelpers,
) {
	// Lower object rest binding patterns in function arguments
	if p.options.unsupportedJSFeatures.Has(compat.ObjectRestSpread) {
		var prefixStmts []ast.Stmt

		// Lower each argument individually instead of lowering all arguments
		// together. There is a correctness tradeoff here around default values
		// for function arguments, with no right answer.
		//
		// Lowering all arguments together will preserve the order of side effects
		// for default values, but will mess up their scope:
		//
		//   // Side effect order: a(), b(), c()
		//   function foo([{[a()]: w, ...x}, y = b()], z = c()) {}
		//
		//   // Side effect order is correct but scope is wrong
		//   function foo(_a, _b) {
		//     var [[{[a()]: w, ...x}, y = b()], z = c()] = [_a, _b]
		//   }
		//
		// Lowering each argument individually will preserve the scope for default
		// values that don't contain object rest binding patterns, but will mess up
		// the side effect order:
		//
		//   // Side effect order: a(), b(), c()
		//   function foo([{[a()]: w, ...x}, y = b()], z = c()) {}
		//
		//   // Side effect order is wrong but scope for c() is correct
		//   function foo(_a, z = c()) {
		//     var [{[a()]: w, ...x}, y = b()] = _a
		//   }
		//
		// This transform chooses to lower each argument individually with the
		// thinking that perhaps scope matters more in real-world code than side
		// effect order.
		for i, arg := range *args {
			if bindingHasObjectRest(arg.Binding) {
				ref := p.generateTempRef(tempRefNoDeclare, "")
				target := ast.ConvertBindingToExpr(arg.Binding, nil)
				init := ast.Expr{Loc: arg.Binding.Loc, Data: &ast.EIdentifier{Ref: ref}}
				p.recordUsage(ref)

				if decls, ok := p.lowerObjectRestToDecls(target, init, nil); ok {
					// Replace the binding but leave the default value intact
					(*args)[i].Binding.Data = &ast.BIdentifier{Ref: ref}

					// Append a variable declaration to the function body
					prefixStmts = append(prefixStmts, ast.Stmt{Loc: arg.Binding.Loc,
						Data: &ast.SLocal{Kind: ast.LocalVar, Decls: decls}})
				}
			}
		}

		if len(prefixStmts) > 0 {
			*bodyStmts = append(prefixStmts, *bodyStmts...)
		}
	}

	// Lower async functions
	if p.options.unsupportedJSFeatures.Has(compat.AsyncAwait) && *isAsync {
		// Use the shortened form if we're an arrow function
		if preferExpr != nil {
			*preferExpr = true
		}

		// Determine the value for "this"
		thisValue, hasThisValue := p.valueForThis(
			bodyLoc,
			false, /* shouldWarn */
			ast.AssignTargetNone,
			false, /* isCallTarget */
			false, /* isDeleteTarget */
		)
		if !hasThisValue {
			thisValue = ast.Expr{Loc: bodyLoc, Data: ast.EThisShared}
		}

		// Move the code into a nested generator function
		fn := ast.Fn{
			IsGenerator: true,
			Body:        ast.FnBody{Loc: bodyLoc, Stmts: *bodyStmts},
		}
		*bodyStmts = nil

		// Errors thrown during argument evaluation must reject the
		// resulting promise, which needs more complex code to handle
		couldThrowErrors := false
		for _, arg := range *args {
			if _, ok := arg.Binding.Data.(*ast.BIdentifier); !ok ||
				(arg.DefaultOrNil.Data != nil && couldPotentiallyThrow(arg.DefaultOrNil.Data)) {
				couldThrowErrors = true
				break
			}
		}

		// Forward the arguments to the wrapper function
		usesArgumentsRef := !isArrow && p.fnOnlyDataVisit.argumentsRef != nil &&
			p.symbolUses[*p.fnOnlyDataVisit.argumentsRef].CountEstimate > 0
		var forwardedArgs ast.Expr
		if !couldThrowErrors && !usesArgumentsRef {
			// Simple case: the arguments can stay on the outer function. It's
			// worth separating out the simple case because it's the common case
			// and it generates smaller code.
			forwardedArgs = ast.Expr{Loc: bodyLoc, Data: ast.ENullShared}
		} else {
			// If code uses "arguments" then we must move the arguments to the inner
			// function. This is because you can modify arguments by assigning to
			// elements in the "arguments" object:
			//
			//   async function foo(x) {
			//     arguments[0] = 1;
			//     // "x" must be 1 here
			//   }
			//

			// Complex case: the arguments must be moved to the inner function
			fn.Args = *args
			fn.HasRestArg = *hasRestArg
			*args = nil
			*hasRestArg = false

			// Make sure to not change the value of the "length" property. This is
			// done by generating dummy arguments for the outer function equal to
			// the expected length of the function:
			//
			//   async function foo(a, b, c = d, ...e) {
			//   }
			//
			// This turns into:
			//
			//   function foo(_0, _1) {
			//     return __async(this, arguments, function* (a, b, c = d, ...e) {
			//     });
			//   }
			//
			// The "_0" and "_1" are dummy variables to ensure "foo.length" is 2.
			for i, arg := range fn.Args {
				if arg.DefaultOrNil.Data != nil || fn.HasRestArg && i+1 == len(fn.Args) {
					// Arguments from here on don't add to the "length"
					break
				}

				// Generate a dummy variable
				argRef := p.newSymbol(ast.SymbolOther, fmt.Sprintf("_%d", i))
				p.currentScope.Generated = append(p.currentScope.Generated, argRef)
				*args = append(*args, ast.Arg{Binding: ast.Binding{Loc: arg.Binding.Loc, Data: &ast.BIdentifier{Ref: argRef}}})
			}

			// Forward all arguments from the outer function to the inner function
			if !isArrow {
				// Normal functions can just use "arguments" to forward everything
				forwardedArgs = ast.Expr{Loc: bodyLoc, Data: &ast.EIdentifier{Ref: *p.fnOnlyDataVisit.argumentsRef}}
			} else {
				// Arrow functions can't use "arguments", so we need to forward
				// the arguments manually.
				//
				// Note that if the arrow function references "arguments" in its body
				// (even if it's inside another nested arrow function), that reference
				// to "arguments" will have to be subsituted with a captured variable.
				// This is because we're changing the arrow function into a generator
				// function, which introduces a variable named "arguments". This is
				// handled separately during symbol resolution instead of being handled
				// here so we don't need to re-traverse the arrow function body.

				// If we need to forward more than the current number of arguments,
				// add a rest argument to the set of forwarding variables. This is the
				// case if the arrow function has rest or default arguments.
				if len(*args) < len(fn.Args) {
					argRef := p.newSymbol(ast.SymbolOther, fmt.Sprintf("_%d", len(*args)))
					p.currentScope.Generated = append(p.currentScope.Generated, argRef)
					*args = append(*args, ast.Arg{Binding: ast.Binding{Loc: bodyLoc, Data: &ast.BIdentifier{Ref: argRef}}})
					*hasRestArg = true
				}

				// Forward all of the arguments
				items := make([]ast.Expr, 0, len(*args))
				for i, arg := range *args {
					id := arg.Binding.Data.(*ast.BIdentifier)
					item := ast.Expr{Loc: arg.Binding.Loc, Data: &ast.EIdentifier{Ref: id.Ref}}
					if *hasRestArg && i+1 == len(*args) {
						item.Data = &ast.ESpread{Value: item}
					}
					items = append(items, item)
				}
				forwardedArgs = ast.Expr{Loc: bodyLoc, Data: &ast.EArray{Items: items, IsSingleLine: true}}
			}
		}

		// "async function foo(a, b) { stmts }" => "function foo(a, b) { return __async(this, null, function* () { stmts }) }"
		*isAsync = false
		callAsync := p.callRuntime(bodyLoc, "__async", []ast.Expr{
			thisValue,
			forwardedArgs,
			{Loc: bodyLoc, Data: &ast.EFunction{Fn: fn}},
		})
		returnStmt := ast.Stmt{Loc: bodyLoc, Data: &ast.SReturn{ValueOrNil: callAsync}}

		// Prepend the "super" index functions if necessary
		var bodyStmtList []ast.Stmt
		if superHelpers != nil {
			if superHelpers.getRef != ast.InvalidRef {
				keyRef := p.newSymbol(ast.SymbolOther, "key")
				p.currentScope.Generated = append(p.currentScope.Generated, superHelpers.getRef, keyRef)
				superGetStmt := ast.Stmt{Loc: bodyLoc, Data: &ast.SLocal{
					Decls: []ast.Decl{{
						Binding: ast.Binding{Loc: bodyLoc, Data: &ast.BIdentifier{Ref: superHelpers.getRef}},
						ValueOrNil: ast.Expr{Loc: bodyLoc, Data: &ast.EArrow{
							Args: []ast.Arg{
								{Binding: ast.Binding{Loc: bodyLoc, Data: &ast.BIdentifier{Ref: keyRef}}},
							},
							Body: ast.FnBody{
								Loc: bodyLoc,
								Stmts: []ast.Stmt{{Loc: bodyLoc, Data: &ast.SReturn{
									ValueOrNil: ast.Expr{Loc: bodyLoc, Data: &ast.EIndex{
										Target: ast.Expr{Loc: bodyLoc, Data: ast.ESuperShared},
										Index:  ast.Expr{Loc: bodyLoc, Data: &ast.EIdentifier{Ref: keyRef}},
									}},
								}}},
							},
							PreferExpr: true,
						}},
					}},
				}}
				p.recordUsage(keyRef)
				bodyStmtList = append(bodyStmtList, superGetStmt)
			}
			if superHelpers.setRef != ast.InvalidRef {
				keyRef := p.newSymbol(ast.SymbolOther, "key")
				valueRef := p.newSymbol(ast.SymbolOther, "value")
				p.currentScope.Generated = append(p.currentScope.Generated, superHelpers.setRef, keyRef)
				p.currentScope.Generated = append(p.currentScope.Generated, superHelpers.setRef, valueRef)
				superSetStmt := ast.Stmt{Loc: bodyLoc, Data: &ast.SLocal{
					Decls: []ast.Decl{{
						Binding: ast.Binding{Loc: bodyLoc, Data: &ast.BIdentifier{Ref: superHelpers.setRef}},
						ValueOrNil: ast.Expr{Loc: bodyLoc, Data: &ast.EArrow{
							Args: []ast.Arg{
								{Binding: ast.Binding{Loc: bodyLoc, Data: &ast.BIdentifier{Ref: keyRef}}},
								{Binding: ast.Binding{Loc: bodyLoc, Data: &ast.BIdentifier{Ref: valueRef}}},
							},
							Body: ast.FnBody{
								Loc: bodyLoc,
								Stmts: []ast.Stmt{{Loc: bodyLoc, Data: &ast.SReturn{
									ValueOrNil: ast.Expr{Loc: bodyLoc, Data: &ast.EBinary{
										Op: ast.BinOpAssign,
										Left: ast.Expr{Loc: bodyLoc, Data: &ast.EIndex{
											Target: ast.Expr{Loc: bodyLoc, Data: ast.ESuperShared},
											Index:  ast.Expr{Loc: bodyLoc, Data: &ast.EIdentifier{Ref: keyRef}},
										}},
										Right: ast.Expr{Loc: bodyLoc, Data: &ast.EIdentifier{Ref: valueRef}},
									}},
								}}},
							},
							PreferExpr: true,
						}},
					}},
				}}
				p.recordUsage(keyRef)
				p.recordUsage(valueRef)
				bodyStmtList = append(bodyStmtList, superSetStmt)
			}
		}
		*bodyStmts = append(bodyStmtList, returnStmt)
	}
}

func (p *parser) lowerOptionalChain(expr ast.Expr, in exprIn, childOut exprOut) (ast.Expr, exprOut) {
	valueWhenUndefined := ast.Expr{Loc: expr.Loc, Data: ast.EUndefinedShared}
	endsWithPropertyAccess := false
	containsPrivateName := false
	startsWithCall := false
	originalExpr := expr
	chain := []ast.Expr{}
	loc := expr.Loc

	// Step 1: Get an array of all expressions in the chain. We're traversing the
	// chain from the outside in, so the array will be filled in "backwards".
flatten:
	for {
		chain = append(chain, expr)

		switch e := expr.Data.(type) {
		case *ast.EDot:
			expr = e.Target
			if len(chain) == 1 {
				endsWithPropertyAccess = true
			}
			if e.OptionalChain == ast.OptionalChainStart {
				break flatten
			}

		case *ast.EIndex:
			expr = e.Target
			if len(chain) == 1 {
				endsWithPropertyAccess = true
			}

			// If this is a private name that needs to be lowered, the entire chain
			// itself will have to be lowered even if the language target supports
			// optional chaining. This is because there's no way to use our shim
			// function for private names with optional chaining syntax.
			if private, ok := e.Index.Data.(*ast.EPrivateIdentifier); ok && p.privateSymbolNeedsToBeLowered(private) {
				containsPrivateName = true
			}

			if e.OptionalChain == ast.OptionalChainStart {
				break flatten
			}

		case *ast.ECall:
			expr = e.Target
			if e.OptionalChain == ast.OptionalChainStart {
				startsWithCall = true
				break flatten
			}

		case *ast.EUnary: // UnOpDelete
			valueWhenUndefined = ast.Expr{Loc: loc, Data: &ast.EBoolean{Value: true}}
			expr = e.Value

		default:
			panic("Internal error")
		}
	}

	// Stop now if we can strip the whole chain as dead code. Since the chain is
	// lazily evaluated, it's safe to just drop the code entirely.
	if p.options.mangleSyntax {
		if isNullOrUndefined, sideEffects, ok := toNullOrUndefinedWithSideEffects(expr.Data); ok && isNullOrUndefined {
			if sideEffects == couldHaveSideEffects {
				return ast.JoinWithComma(p.simplifyUnusedExpr(expr), valueWhenUndefined), exprOut{}
			}
			return valueWhenUndefined, exprOut{}
		}
	} else {
		switch expr.Data.(type) {
		case *ast.ENull, *ast.EUndefined:
			return valueWhenUndefined, exprOut{}
		}
	}

	// We need to lower this if this is an optional call off of a private name
	// such as "foo.#bar?.()" because the value of "this" must be captured.
	if _, _, private := p.extractPrivateIndex(expr); private != nil {
		containsPrivateName = true
	}

	// Don't lower this if we don't need to. This check must be done here instead
	// of earlier so we can do the dead code elimination above when the target is
	// null or undefined.
	if !p.options.unsupportedJSFeatures.Has(compat.OptionalChain) && !containsPrivateName {
		return originalExpr, exprOut{}
	}

	// Step 2: Figure out if we need to capture the value for "this" for the
	// initial ECall. This will be passed to ".call(this, ...args)" later.
	var thisArg ast.Expr
	var targetWrapFunc func(ast.Expr) ast.Expr
	if startsWithCall {
		if childOut.thisArgFunc != nil {
			// The initial value is a nested optional chain that ended in a property
			// access. The nested chain was processed first and has saved the
			// appropriate value for "this". The callback here will return a
			// reference to that saved location.
			thisArg = childOut.thisArgFunc()
		} else {
			// The initial value is a normal expression. If it's a property access,
			// strip the property off and save the target of the property access to
			// be used as the value for "this".
			switch e := expr.Data.(type) {
			case *ast.EDot:
				if _, ok := e.Target.Data.(*ast.ESuper); ok {
					// Lower "super.prop" if necessary
					if p.shouldLowerSuperPropertyAccess(e.Target) {
						key := ast.Expr{Loc: e.NameLoc, Data: &ast.EString{Value: lexer.StringToUTF16(e.Name)}}
						expr = p.lowerSuperPropertyGet(expr.Loc, key)
					}

					// Special-case "super.foo?.()" to avoid a syntax error. Without this,
					// we would generate:
					//
					//   (_b = (_a = super).foo) == null ? void 0 : _b.call(_a)
					//
					// which is a syntax error. Now we generate this instead:
					//
					//   (_a = super.foo) == null ? void 0 : _a.call(this)
					//
					thisArg = ast.Expr{Loc: loc, Data: ast.EThisShared}
				} else {
					targetFunc, wrapFunc := p.captureValueWithPossibleSideEffects(loc, 2, e.Target, valueDefinitelyNotMutated)
					expr = ast.Expr{Loc: loc, Data: &ast.EDot{
						Target:  targetFunc(),
						Name:    e.Name,
						NameLoc: e.NameLoc,
					}}
					thisArg = targetFunc()
					targetWrapFunc = wrapFunc
				}

			case *ast.EIndex:
				if _, ok := e.Target.Data.(*ast.ESuper); ok {
					// Lower "super[prop]" if necessary
					if p.shouldLowerSuperPropertyAccess(e.Target) {
						expr = p.lowerSuperPropertyGet(expr.Loc, e.Index)
					}

					// See the comment above about a similar special case for EDot
					thisArg = ast.Expr{Loc: loc, Data: ast.EThisShared}
				} else {
					targetFunc, wrapFunc := p.captureValueWithPossibleSideEffects(loc, 2, e.Target, valueDefinitelyNotMutated)
					targetWrapFunc = wrapFunc

					// Capture the value of "this" if the target of the starting call
					// expression is a private property access
					if private, ok := e.Index.Data.(*ast.EPrivateIdentifier); ok && p.privateSymbolNeedsToBeLowered(private) {
						// "foo().#bar?.()" must capture "foo()" for "this"
						expr = p.lowerPrivateGet(targetFunc(), e.Index.Loc, private)
						thisArg = targetFunc()
						break
					}

					expr = ast.Expr{Loc: loc, Data: &ast.EIndex{
						Target: targetFunc(),
						Index:  e.Index,
					}}
					thisArg = targetFunc()
				}
			}
		}
	}

	// Step 3: Figure out if we need to capture the starting value. We don't need
	// to capture it if it doesn't have any side effects (e.g. it's just a bare
	// identifier). Skipping the capture reduces code size and matches the output
	// of the TypeScript compiler.
	exprFunc, exprWrapFunc := p.captureValueWithPossibleSideEffects(loc, 2, expr, valueDefinitelyNotMutated)
	expr = exprFunc()
	result := exprFunc()

	// Step 4: Wrap the starting value by each expression in the chain. We
	// traverse the chain in reverse because we want to go from the inside out
	// and the chain was built from the outside in.
	var parentThisArgFunc func() ast.Expr
	var parentThisArgWrapFunc func(ast.Expr) ast.Expr
	var privateThisFunc func() ast.Expr
	var privateThisWrapFunc func(ast.Expr) ast.Expr
	for i := len(chain) - 1; i >= 0; i-- {
		// Save a reference to the value of "this" for our parent ECall
		if i == 0 && in.storeThisArgForParentOptionalChain && endsWithPropertyAccess {
			parentThisArgFunc, parentThisArgWrapFunc = p.captureValueWithPossibleSideEffects(result.Loc, 2, result, valueDefinitelyNotMutated)
			result = parentThisArgFunc()
		}

		switch e := chain[i].Data.(type) {
		case *ast.EDot:
			result = ast.Expr{Loc: loc, Data: &ast.EDot{
				Target:  result,
				Name:    e.Name,
				NameLoc: e.NameLoc,
			}}

		case *ast.EIndex:
			if private, ok := e.Index.Data.(*ast.EPrivateIdentifier); ok && p.privateSymbolNeedsToBeLowered(private) {
				// If this is private name property access inside a call expression and
				// the call expression is part of this chain, then the call expression
				// is going to need a copy of the property access target as the value
				// for "this" for the call. Example for this case: "foo.#bar?.()"
				if i > 0 {
					if _, ok := chain[i-1].Data.(*ast.ECall); ok {
						privateThisFunc, privateThisWrapFunc = p.captureValueWithPossibleSideEffects(loc, 2, result, valueDefinitelyNotMutated)
						result = privateThisFunc()
					}
				}

				result = p.lowerPrivateGet(result, e.Index.Loc, private)
				continue
			}

			result = ast.Expr{Loc: loc, Data: &ast.EIndex{
				Target: result,
				Index:  e.Index,
			}}

		case *ast.ECall:
			// If this is the initial ECall in the chain and it's being called off of
			// a property access, invoke the function using ".call(this, ...args)" to
			// explicitly provide the value for "this".
			if i == len(chain)-1 && thisArg.Data != nil {
				result = ast.Expr{Loc: loc, Data: &ast.ECall{
					Target: ast.Expr{Loc: loc, Data: &ast.EDot{
						Target:  result,
						Name:    "call",
						NameLoc: loc,
					}},
					Args:                   append([]ast.Expr{thisArg}, e.Args...),
					CanBeUnwrappedIfUnused: e.CanBeUnwrappedIfUnused,
				}}
				break
			}

			// If the target of this call expression is a private name property
			// access that's also part of this chain, then we must use the copy of
			// the property access target that was stashed away earlier as the value
			// for "this" for the call. Example for this case: "foo.#bar?.()"
			if privateThisFunc != nil {
				result = privateThisWrapFunc(ast.Expr{Loc: loc, Data: &ast.ECall{
					Target: ast.Expr{Loc: loc, Data: &ast.EDot{
						Target:  result,
						Name:    "call",
						NameLoc: loc,
					}},
					Args:                   append([]ast.Expr{privateThisFunc()}, e.Args...),
					CanBeUnwrappedIfUnused: e.CanBeUnwrappedIfUnused,
				}})
				privateThisFunc = nil
				break
			}

			result = ast.Expr{Loc: loc, Data: &ast.ECall{
				Target:                 result,
				Args:                   e.Args,
				CanBeUnwrappedIfUnused: e.CanBeUnwrappedIfUnused,
			}}

		case *ast.EUnary:
			result = ast.Expr{Loc: loc, Data: &ast.EUnary{
				Op:    ast.UnOpDelete,
				Value: result,
			}}

		default:
			panic("Internal error")
		}
	}

	// Step 5: Wrap it all in a conditional that returns the chain or the default
	// value if the initial value is null/undefined. The default value is usually
	// "undefined" but is "true" if the chain ends in a "delete" operator.
	// "x?.y" => "x == null ? void 0 : x.y"
	// "x()?.y()" => "(_a = x()) == null ? void 0 : _a.y()"
	result = ast.Expr{Loc: loc, Data: &ast.EIf{
		Test: ast.Expr{Loc: loc, Data: &ast.EBinary{
			Op:    ast.BinOpLooseEq,
			Left:  expr,
			Right: ast.Expr{Loc: loc, Data: ast.ENullShared},
		}},
		Yes: valueWhenUndefined,
		No:  result,
	}}
	if exprWrapFunc != nil {
		result = exprWrapFunc(result)
	}
	if targetWrapFunc != nil {
		result = targetWrapFunc(result)
	}
	if childOut.thisArgWrapFunc != nil {
		result = childOut.thisArgWrapFunc(result)
	}
	return result, exprOut{
		thisArgFunc:     parentThisArgFunc,
		thisArgWrapFunc: parentThisArgWrapFunc,
	}
}

func (p *parser) lowerParenthesizedOptionalChain(loc logger.Loc, e *ast.ECall, childOut exprOut) ast.Expr {
	return childOut.thisArgWrapFunc(ast.Expr{Loc: loc, Data: &ast.ECall{
		Target: ast.Expr{Loc: loc, Data: &ast.EDot{
			Target:  e.Target,
			Name:    "call",
			NameLoc: loc,
		}},
		Args: append(append(make([]ast.Expr, 0, len(e.Args)+1), childOut.thisArgFunc()), e.Args...),
	}})
}

func (p *parser) lowerAssignmentOperator(value ast.Expr, callback func(ast.Expr, ast.Expr) ast.Expr) ast.Expr {
	switch left := value.Data.(type) {
	case *ast.EDot:
		if left.OptionalChain == ast.OptionalChainNone {
			referenceFunc, wrapFunc := p.captureValueWithPossibleSideEffects(value.Loc, 2, left.Target, valueDefinitelyNotMutated)
			return wrapFunc(callback(
				ast.Expr{Loc: value.Loc, Data: &ast.EDot{
					Target:  referenceFunc(),
					Name:    left.Name,
					NameLoc: left.NameLoc,
				}},
				ast.Expr{Loc: value.Loc, Data: &ast.EDot{
					Target:  referenceFunc(),
					Name:    left.Name,
					NameLoc: left.NameLoc,
				}},
			))
		}

	case *ast.EIndex:
		if left.OptionalChain == ast.OptionalChainNone {
			targetFunc, targetWrapFunc := p.captureValueWithPossibleSideEffects(value.Loc, 2, left.Target, valueDefinitelyNotMutated)
			indexFunc, indexWrapFunc := p.captureValueWithPossibleSideEffects(value.Loc, 2, left.Index, valueDefinitelyNotMutated)
			return targetWrapFunc(indexWrapFunc(callback(
				ast.Expr{Loc: value.Loc, Data: &ast.EIndex{
					Target: targetFunc(),
					Index:  indexFunc(),
				}},
				ast.Expr{Loc: value.Loc, Data: &ast.EIndex{
					Target: targetFunc(),
					Index:  indexFunc(),
				}},
			)))
		}

	case *ast.EIdentifier:
		return callback(
			ast.Expr{Loc: value.Loc, Data: &ast.EIdentifier{Ref: left.Ref}},
			value,
		)
	}

	// We shouldn't get here with valid syntax? Just let this through for now
	// since there's currently no assignment target validation. Garbage in,
	// garbage out.
	return value
}

func (p *parser) lowerExponentiationAssignmentOperator(loc logger.Loc, e *ast.EBinary) ast.Expr {
	if target, privateLoc, private := p.extractPrivateIndex(e.Left); private != nil {
		// "a.#b **= c" => "__privateSet(a, #b, __pow(__privateGet(a, #b), c))"
		targetFunc, targetWrapFunc := p.captureValueWithPossibleSideEffects(loc, 2, target, valueDefinitelyNotMutated)
		return targetWrapFunc(p.lowerPrivateSet(targetFunc(), privateLoc, private,
			p.callRuntime(loc, "__pow", []ast.Expr{
				p.lowerPrivateGet(targetFunc(), privateLoc, private),
				e.Right,
			})))
	}

	return p.lowerAssignmentOperator(e.Left, func(a ast.Expr, b ast.Expr) ast.Expr {
		// "a **= b" => "a = __pow(a, b)"
		return ast.Assign(a, p.callRuntime(loc, "__pow", []ast.Expr{b, e.Right}))
	})
}

func (p *parser) lowerNullishCoalescingAssignmentOperator(loc logger.Loc, e *ast.EBinary) (ast.Expr, bool) {
	if target, privateLoc, private := p.extractPrivateIndex(e.Left); private != nil {
		if p.options.unsupportedJSFeatures.Has(compat.NullishCoalescing) {
			// "a.#b ??= c" => "(_a = __privateGet(a, #b)) != null ? _a : __privateSet(a, #b, c)"
			targetFunc, targetWrapFunc := p.captureValueWithPossibleSideEffects(loc, 2, target, valueDefinitelyNotMutated)
			left := p.lowerPrivateGet(targetFunc(), privateLoc, private)
			right := p.lowerPrivateSet(targetFunc(), privateLoc, private, e.Right)
			return targetWrapFunc(p.lowerNullishCoalescing(loc, left, right)), true
		}

		// "a.#b ??= c" => "__privateGet(a, #b) ?? __privateSet(a, #b, c)"
		targetFunc, targetWrapFunc := p.captureValueWithPossibleSideEffects(loc, 2, target, valueDefinitelyNotMutated)
		return targetWrapFunc(ast.Expr{Loc: loc, Data: &ast.EBinary{
			Op:    ast.BinOpNullishCoalescing,
			Left:  p.lowerPrivateGet(targetFunc(), privateLoc, private),
			Right: p.lowerPrivateSet(targetFunc(), privateLoc, private, e.Right),
		}}), true
	}

	if p.options.unsupportedJSFeatures.Has(compat.LogicalAssignment) {
		return p.lowerAssignmentOperator(e.Left, func(a ast.Expr, b ast.Expr) ast.Expr {
			if p.options.unsupportedJSFeatures.Has(compat.NullishCoalescing) {
				// "a ??= b" => "(_a = a) != null ? _a : a = b"
				return p.lowerNullishCoalescing(loc, a, ast.Assign(b, e.Right))
			}

			// "a ??= b" => "a ?? (a = b)"
			return ast.Expr{Loc: loc, Data: &ast.EBinary{
				Op:    ast.BinOpNullishCoalescing,
				Left:  a,
				Right: ast.Assign(b, e.Right),
			}}
		}), true
	}

	return ast.Expr{}, false
}

func (p *parser) lowerLogicalAssignmentOperator(loc logger.Loc, e *ast.EBinary, op ast.OpCode) (ast.Expr, bool) {
	if target, privateLoc, private := p.extractPrivateIndex(e.Left); private != nil {
		// "a.#b &&= c" => "__privateGet(a, #b) && __privateSet(a, #b, c)"
		// "a.#b ||= c" => "__privateGet(a, #b) || __privateSet(a, #b, c)"
		targetFunc, targetWrapFunc := p.captureValueWithPossibleSideEffects(loc, 2, target, valueDefinitelyNotMutated)
		return targetWrapFunc(ast.Expr{Loc: loc, Data: &ast.EBinary{
			Op:    op,
			Left:  p.lowerPrivateGet(targetFunc(), privateLoc, private),
			Right: p.lowerPrivateSet(targetFunc(), privateLoc, private, e.Right),
		}}), true
	}

	if p.options.unsupportedJSFeatures.Has(compat.LogicalAssignment) {
		return p.lowerAssignmentOperator(e.Left, func(a ast.Expr, b ast.Expr) ast.Expr {
			// "a &&= b" => "a && (a = b)"
			// "a ||= b" => "a || (a = b)"
			return ast.Expr{Loc: loc, Data: &ast.EBinary{
				Op:    op,
				Left:  a,
				Right: ast.Assign(b, e.Right),
			}}
		}), true
	}

	return ast.Expr{}, false
}

func (p *parser) lowerNullishCoalescing(loc logger.Loc, left ast.Expr, right ast.Expr) ast.Expr {
	// "x ?? y" => "x != null ? x : y"
	// "x() ?? y()" => "_a = x(), _a != null ? _a : y"
	leftFunc, wrapFunc := p.captureValueWithPossibleSideEffects(loc, 2, left, valueDefinitelyNotMutated)
	return wrapFunc(ast.Expr{Loc: loc, Data: &ast.EIf{
		Test: ast.Expr{Loc: loc, Data: &ast.EBinary{
			Op:    ast.BinOpLooseNe,
			Left:  leftFunc(),
			Right: ast.Expr{Loc: loc, Data: ast.ENullShared},
		}},
		Yes: leftFunc(),
		No:  right,
	}})
}

// Lower object spread for environments that don't support them. Non-spread
// properties are grouped into object literals and then passed to the
// "__spreadValues" and "__spreadProps" functions like this:
//
//   "{a, b, ...c, d, e}" => "__spreadProps(__spreadValues(__spreadProps({a, b}, c), {d, e})"
//
// If the object literal starts with a spread, then we pass an empty object
// literal to "__spreadValues" to make sure we clone the object:
//
//   "{...a, b}" => "__spreadProps(__spreadValues({}, a), {b})"
//
// It's not immediately obvious why we don't compile everything to a single
// call to a function that takes any number of arguments, since that would be
// shorter. The reason is to preserve the order of side effects. Consider
// this code:
//
//   let a = {
//     get x() {
//       b = {y: 2}
//       return 1
//     }
//   }
//   let b = {}
//   let c = {...a, ...b}
//
// Converting the above code to "let c = __spreadFn({}, a, null, b)" means "c"
// becomes "{x: 1}" which is incorrect. Converting the above code instead to
// "let c = __spreadProps(__spreadProps({}, a), b)" means "c" becomes
// "{x: 1, y: 2}" which is correct.
func (p *parser) lowerObjectSpread(loc logger.Loc, e *ast.EObject) ast.Expr {
	needsLowering := false

	if p.options.unsupportedJSFeatures.Has(compat.ObjectRestSpread) {
		for _, property := range e.Properties {
			if property.Kind == ast.PropertySpread {
				needsLowering = true
				break
			}
		}
	}

	if !needsLowering {
		return ast.Expr{Loc: loc, Data: e}
	}

	var result ast.Expr
	properties := []ast.Property{}

	for _, property := range e.Properties {
		if property.Kind != ast.PropertySpread {
			properties = append(properties, property)
			continue
		}

		if len(properties) > 0 || result.Data == nil {
			if result.Data == nil {
				// "{a, ...b}" => "__spreadValues({a}, b)"
				result = ast.Expr{Loc: loc, Data: &ast.EObject{
					Properties:   properties,
					IsSingleLine: e.IsSingleLine,
				}}
			} else {
				// "{...a, b, ...c}" => "__spreadValues(__spreadProps(__spreadValues({}, a), {b}), c)"
				result = p.callRuntime(loc, "__spreadProps",
					[]ast.Expr{result, {Loc: loc, Data: &ast.EObject{
						Properties:   properties,
						IsSingleLine: e.IsSingleLine,
					}}})
			}
			properties = []ast.Property{}
		}

		// "{a, ...b}" => "__spreadValues({a}, b)"
		result = p.callRuntime(loc, "__spreadValues", []ast.Expr{result, property.ValueOrNil})
	}

	if len(properties) > 0 {
		// "{...a, b}" => "__spreadProps(__spreadValues({}, a), {b})"
		result = p.callRuntime(loc, "__spreadProps", []ast.Expr{result, {Loc: loc, Data: &ast.EObject{
			Properties:   properties,
			IsSingleLine: e.IsSingleLine,
		}}})
	}

	return result
}

func (p *parser) lowerPrivateBrandCheck(target ast.Expr, loc logger.Loc, private *ast.EPrivateIdentifier) ast.Expr {
	// "#field in this" => "__privateIn(#field, this)"
	return p.callRuntime(loc, "__privateIn", []ast.Expr{
		{Loc: loc, Data: &ast.EIdentifier{Ref: private.Ref}},
		target,
	})
}

func (p *parser) lowerPrivateGet(target ast.Expr, loc logger.Loc, private *ast.EPrivateIdentifier) ast.Expr {
	switch p.symbols[private.Ref.InnerIndex].Kind {
	case ast.SymbolPrivateMethod, ast.SymbolPrivateStaticMethod:
		// "this.#method" => "__privateMethod(this, #method, method_fn)"
		fnRef := p.privateGetters[private.Ref]
		p.recordUsage(fnRef)
		return p.callRuntime(target.Loc, "__privateMethod", []ast.Expr{
			target,
			{Loc: loc, Data: &ast.EIdentifier{Ref: private.Ref}},
			{Loc: loc, Data: &ast.EIdentifier{Ref: fnRef}},
		})

	case ast.SymbolPrivateGet, ast.SymbolPrivateStaticGet,
		ast.SymbolPrivateGetSetPair, ast.SymbolPrivateStaticGetSetPair:
		// "this.#getter" => "__privateGet(this, #getter, getter_get)"
		fnRef := p.privateGetters[private.Ref]
		p.recordUsage(fnRef)
		return p.callRuntime(target.Loc, "__privateGet", []ast.Expr{
			target,
			{Loc: loc, Data: &ast.EIdentifier{Ref: private.Ref}},
			{Loc: loc, Data: &ast.EIdentifier{Ref: fnRef}},
		})

	default:
		// "this.#field" => "__privateGet(this, #field)"
		return p.callRuntime(target.Loc, "__privateGet", []ast.Expr{
			target,
			{Loc: loc, Data: &ast.EIdentifier{Ref: private.Ref}},
		})
	}
}

func (p *parser) lowerPrivateSet(
	target ast.Expr,
	loc logger.Loc,
	private *ast.EPrivateIdentifier,
	value ast.Expr,
) ast.Expr {
	switch p.symbols[private.Ref.InnerIndex].Kind {
	case ast.SymbolPrivateSet, ast.SymbolPrivateStaticSet,
		ast.SymbolPrivateGetSetPair, ast.SymbolPrivateStaticGetSetPair:
		// "this.#setter = 123" => "__privateSet(this, #setter, 123, setter_set)"
		fnRef := p.privateSetters[private.Ref]
		p.recordUsage(fnRef)
		return p.callRuntime(target.Loc, "__privateSet", []ast.Expr{
			target,
			{Loc: loc, Data: &ast.EIdentifier{Ref: private.Ref}},
			value,
			{Loc: loc, Data: &ast.EIdentifier{Ref: fnRef}},
		})

	default:
		// "this.#field = 123" => "__privateSet(this, #field, 123)"
		return p.callRuntime(target.Loc, "__privateSet", []ast.Expr{
			target,
			{Loc: loc, Data: &ast.EIdentifier{Ref: private.Ref}},
			value,
		})
	}
}

func (p *parser) lowerPrivateSetUnOp(target ast.Expr, loc logger.Loc, private *ast.EPrivateIdentifier, op ast.OpCode) ast.Expr {
	kind := p.symbols[private.Ref.InnerIndex].Kind

	// Determine the setter, if any
	var setter ast.Expr
	switch kind {
	case ast.SymbolPrivateSet, ast.SymbolPrivateStaticSet,
		ast.SymbolPrivateGetSetPair, ast.SymbolPrivateStaticGetSetPair:
		ref := p.privateSetters[private.Ref]
		p.recordUsage(ref)
		setter = ast.Expr{Loc: loc, Data: &ast.EIdentifier{Ref: ref}}
	}

	// Determine the getter, if any
	var getter ast.Expr
	switch kind {
	case ast.SymbolPrivateGet, ast.SymbolPrivateStaticGet,
		ast.SymbolPrivateGetSetPair, ast.SymbolPrivateStaticGetSetPair:
		ref := p.privateGetters[private.Ref]
		p.recordUsage(ref)
		getter = ast.Expr{Loc: loc, Data: &ast.EIdentifier{Ref: ref}}
	}

	// Only include necessary arguments
	args := []ast.Expr{
		target,
		{Loc: loc, Data: &ast.EIdentifier{Ref: private.Ref}},
	}
	if setter.Data != nil {
		args = append(args, setter)
	}
	if getter.Data != nil {
		if setter.Data == nil {
			args = append(args, ast.Expr{Loc: loc, Data: ast.ENullShared})
		}
		args = append(args, getter)
	}

	// "target.#private++" => "__privateWrapper(target, #private, private_set, private_get)._++"
	return ast.Expr{Loc: loc, Data: &ast.EUnary{
		Op: op,
		Value: ast.Expr{Loc: target.Loc, Data: &ast.EDot{
			Target:  p.callRuntime(target.Loc, "__privateWrapper", args),
			NameLoc: target.Loc,
			Name:    "_",
		}},
	}}
}

func (p *parser) lowerPrivateSetBinOp(target ast.Expr, loc logger.Loc, private *ast.EPrivateIdentifier, op ast.OpCode, value ast.Expr) ast.Expr {
	// "target.#private += 123" => "__privateSet(target, #private, __privateGet(target, #private) + 123)"
	targetFunc, targetWrapFunc := p.captureValueWithPossibleSideEffects(target.Loc, 2, target, valueDefinitelyNotMutated)
	return targetWrapFunc(p.lowerPrivateSet(targetFunc(), loc, private, ast.Expr{Loc: value.Loc, Data: &ast.EBinary{
		Op:    op,
		Left:  p.lowerPrivateGet(targetFunc(), loc, private),
		Right: value,
	}}))
}

// Returns valid data if target is an expression of the form "foo.#bar" and if
// the language target is such that private members must be lowered
func (p *parser) extractPrivateIndex(target ast.Expr) (ast.Expr, logger.Loc, *ast.EPrivateIdentifier) {
	if index, ok := target.Data.(*ast.EIndex); ok {
		if private, ok := index.Index.Data.(*ast.EPrivateIdentifier); ok && p.privateSymbolNeedsToBeLowered(private) {
			return index.Target, index.Index.Loc, private
		}
	}
	return ast.Expr{}, logger.Loc{}, nil
}

// Returns a valid property if target is an expression of the form "super.bar"
// or "super[bar]" and if the situation is such that it must be lowered
func (p *parser) extractSuperProperty(target ast.Expr) ast.Expr {
	switch e := target.Data.(type) {
	case *ast.EDot:
		if p.shouldLowerSuperPropertyAccess(e.Target) {
			return ast.Expr{Loc: e.NameLoc, Data: &ast.EString{Value: lexer.StringToUTF16(e.Name)}}
		}
	case *ast.EIndex:
		if p.shouldLowerSuperPropertyAccess(e.Target) {
			return e.Index
		}
	}
	return ast.Expr{}
}

func bindingHasObjectRest(binding ast.Binding) bool {
	switch b := binding.Data.(type) {
	case *ast.BArray:
		for _, item := range b.Items {
			if bindingHasObjectRest(item.Binding) {
				return true
			}
		}
	case *ast.BObject:
		for _, property := range b.Properties {
			if property.IsSpread || bindingHasObjectRest(property.Value) {
				return true
			}
		}
	}
	return false
}

func exprHasObjectRest(expr ast.Expr) bool {
	switch e := expr.Data.(type) {
	case *ast.EBinary:
		if e.Op == ast.BinOpAssign && exprHasObjectRest(e.Left) {
			return true
		}
	case *ast.EArray:
		for _, item := range e.Items {
			if exprHasObjectRest(item) {
				return true
			}
		}
	case *ast.EObject:
		for _, property := range e.Properties {
			if property.Kind == ast.PropertySpread || exprHasObjectRest(property.ValueOrNil) {
				return true
			}
		}
	}
	return false
}

func (p *parser) lowerObjectRestInDecls(decls []ast.Decl) []ast.Decl {
	if !p.options.unsupportedJSFeatures.Has(compat.ObjectRestSpread) {
		return decls
	}

	// Don't do any allocations if there are no object rest patterns. We want as
	// little overhead as possible in the common case.
	for i, decl := range decls {
		if decl.ValueOrNil.Data != nil && bindingHasObjectRest(decl.Binding) {
			clone := append([]ast.Decl{}, decls[:i]...)
			for _, decl := range decls[i:] {
				if decl.ValueOrNil.Data != nil {
					target := ast.ConvertBindingToExpr(decl.Binding, nil)
					if result, ok := p.lowerObjectRestToDecls(target, decl.ValueOrNil, clone); ok {
						clone = result
						continue
					}
				}
				clone = append(clone, decl)
			}

			return clone
		}
	}

	return decls
}

func (p *parser) lowerObjectRestInForLoopInit(init ast.Stmt, body *ast.Stmt) {
	if !p.options.unsupportedJSFeatures.Has(compat.ObjectRestSpread) {
		return
	}

	var bodyPrefixStmt ast.Stmt

	switch s := init.Data.(type) {
	case *ast.SExpr:
		// "for ({...x} in y) {}"
		// "for ({...x} of y) {}"
		if exprHasObjectRest(s.Value) {
			ref := p.generateTempRef(tempRefNeedsDeclare, "")
			if expr, ok := p.lowerAssign(s.Value, ast.Expr{Loc: init.Loc, Data: &ast.EIdentifier{Ref: ref}}, objRestReturnValueIsUnused); ok {
				s.Value.Data = &ast.EIdentifier{Ref: ref}
				bodyPrefixStmt = ast.Stmt{Loc: expr.Loc, Data: &ast.SExpr{Value: expr}}
			}
		}

	case *ast.SLocal:
		// "for (let {...x} in y) {}"
		// "for (let {...x} of y) {}"
		if len(s.Decls) == 1 && bindingHasObjectRest(s.Decls[0].Binding) {
			ref := p.generateTempRef(tempRefNoDeclare, "")
			decl := ast.Decl{Binding: s.Decls[0].Binding, ValueOrNil: ast.Expr{Loc: init.Loc, Data: &ast.EIdentifier{Ref: ref}}}
			p.recordUsage(ref)
			decls := p.lowerObjectRestInDecls([]ast.Decl{decl})
			s.Decls[0].Binding.Data = &ast.BIdentifier{Ref: ref}
			bodyPrefixStmt = ast.Stmt{Loc: init.Loc, Data: &ast.SLocal{Kind: s.Kind, Decls: decls}}
		}
	}

	if bodyPrefixStmt.Data != nil {
		if block, ok := body.Data.(*ast.SBlock); ok {
			// If there's already a block, insert at the front
			stmts := make([]ast.Stmt, 0, 1+len(block.Stmts))
			block.Stmts = append(append(stmts, bodyPrefixStmt), block.Stmts...)
		} else {
			// Otherwise, make a block and insert at the front
			body.Data = &ast.SBlock{Stmts: []ast.Stmt{bodyPrefixStmt, *body}}
		}
	}
}

func (p *parser) lowerObjectRestInCatchBinding(catch *ast.Catch) {
	if !p.options.unsupportedJSFeatures.Has(compat.ObjectRestSpread) {
		return
	}

	if catch.BindingOrNil.Data != nil && bindingHasObjectRest(catch.BindingOrNil) {
		ref := p.generateTempRef(tempRefNoDeclare, "")
		decl := ast.Decl{Binding: catch.BindingOrNil, ValueOrNil: ast.Expr{Loc: catch.BindingOrNil.Loc, Data: &ast.EIdentifier{Ref: ref}}}
		p.recordUsage(ref)
		decls := p.lowerObjectRestInDecls([]ast.Decl{decl})
		catch.BindingOrNil.Data = &ast.BIdentifier{Ref: ref}
		stmts := make([]ast.Stmt, 0, 1+len(catch.Body))
		stmts = append(stmts, ast.Stmt{Loc: catch.BindingOrNil.Loc, Data: &ast.SLocal{Kind: ast.LocalLet, Decls: decls}})
		catch.Body = append(stmts, catch.Body...)
	}
}

type objRestMode uint8

const (
	objRestReturnValueIsUnused objRestMode = iota
	objRestMustReturnInitExpr
)

func (p *parser) lowerAssign(rootExpr ast.Expr, rootInit ast.Expr, mode objRestMode) (ast.Expr, bool) {
	rootExpr, didLower := p.lowerSuperPropertyOrPrivateInAssign(rootExpr)

	var expr ast.Expr
	assign := func(left ast.Expr, right ast.Expr) {
		expr = ast.JoinWithComma(expr, ast.Assign(left, right))
	}

	if initWrapFunc, ok := p.lowerObjectRestHelper(rootExpr, rootInit, assign, tempRefNeedsDeclare, mode); ok {
		if initWrapFunc != nil {
			expr = initWrapFunc(expr)
		}
		return expr, true
	}

	if didLower {
		return ast.Assign(rootExpr, rootInit), true
	}

	return ast.Expr{}, false
}

func (p *parser) lowerSuperPropertyOrPrivateInAssign(expr ast.Expr) (ast.Expr, bool) {
	didLower := false

	switch e := expr.Data.(type) {
	case *ast.ESpread:
		if value, ok := p.lowerSuperPropertyOrPrivateInAssign(e.Value); ok {
			e.Value = value
			didLower = true
		}

	case *ast.EDot:
		// "[super.foo] = [bar]" => "[__superWrapper(this, 'foo')._] = [bar]"
		if p.shouldLowerSuperPropertyAccess(e.Target) {
			key := ast.Expr{Loc: e.NameLoc, Data: &ast.EString{Value: lexer.StringToUTF16(e.Name)}}
			expr = p.callSuperPropertyWrapper(expr.Loc, key, false /* includeGet */)
			didLower = true
		}

	case *ast.EIndex:
		// "[super[foo]] = [bar]" => "[__superWrapper(this, foo)._] = [bar]"
		if p.shouldLowerSuperPropertyAccess(e.Target) {
			expr = p.callSuperPropertyWrapper(expr.Loc, e.Index, false /* includeGet */)
			didLower = true
			break
		}

		// "[a.#b] = [c]" => "[__privateWrapper(a, #b)._] = [c]"
		if private, ok := e.Index.Data.(*ast.EPrivateIdentifier); ok && p.privateSymbolNeedsToBeLowered(private) {
			var target ast.Expr

			switch p.symbols[private.Ref.InnerIndex].Kind {
			case ast.SymbolPrivateSet, ast.SymbolPrivateStaticSet,
				ast.SymbolPrivateGetSetPair, ast.SymbolPrivateStaticGetSetPair:
				// "this.#setter" => "__privateWrapper(this, #setter, setter_set)"
				fnRef := p.privateSetters[private.Ref]
				p.recordUsage(fnRef)
				target = p.callRuntime(expr.Loc, "__privateWrapper", []ast.Expr{
					e.Target,
					{Loc: expr.Loc, Data: &ast.EIdentifier{Ref: private.Ref}},
					{Loc: expr.Loc, Data: &ast.EIdentifier{Ref: fnRef}},
				})

			default:
				// "this.#field" => "__privateWrapper(this, #field)"
				target = p.callRuntime(expr.Loc, "__privateWrapper", []ast.Expr{
					e.Target,
					{Loc: expr.Loc, Data: &ast.EIdentifier{Ref: private.Ref}},
				})
			}

			// "__privateWrapper(this, #field)" => "__privateWrapper(this, #field)._"
			expr.Data = &ast.EDot{Target: target, Name: "_", NameLoc: expr.Loc}
			didLower = true
		}

	case *ast.EArray:
		for i, item := range e.Items {
			if item, ok := p.lowerSuperPropertyOrPrivateInAssign(item); ok {
				e.Items[i] = item
				didLower = true
			}
		}

	case *ast.EObject:
		for i, property := range e.Properties {
			if property.ValueOrNil.Data != nil {
				if value, ok := p.lowerSuperPropertyOrPrivateInAssign(property.ValueOrNil); ok {
					e.Properties[i].ValueOrNil = value
					didLower = true
				}
			}
		}
	}

	return expr, didLower
}

func (p *parser) lowerObjectRestToDecls(rootExpr ast.Expr, rootInit ast.Expr, decls []ast.Decl) ([]ast.Decl, bool) {
	assign := func(left ast.Expr, right ast.Expr) {
		binding, invalidLog := p.convertExprToBinding(left, invalidLog{})
		if len(invalidLog.invalidTokens) > 0 {
			panic("Internal error")
		}
		decls = append(decls, ast.Decl{Binding: binding, ValueOrNil: right})
	}

	if _, ok := p.lowerObjectRestHelper(rootExpr, rootInit, assign, tempRefNoDeclare, objRestReturnValueIsUnused); ok {
		return decls, true
	}

	return nil, false
}

func (p *parser) lowerObjectRestHelper(
	rootExpr ast.Expr,
	rootInit ast.Expr,
	assign func(ast.Expr, ast.Expr),
	declare generateTempRefArg,
	mode objRestMode,
) (wrapFunc func(ast.Expr) ast.Expr, ok bool) {
	if !p.options.unsupportedJSFeatures.Has(compat.ObjectRestSpread) {
		return nil, false
	}

	// Check if this could possibly contain an object rest binding
	switch rootExpr.Data.(type) {
	case *ast.EArray, *ast.EObject:
	default:
		return nil, false
	}

	// Scan for object rest bindings and initalize rest binding containment
	containsRestBinding := make(map[ast.E]bool)
	var findRestBindings func(ast.Expr) bool
	findRestBindings = func(expr ast.Expr) bool {
		found := false
		switch e := expr.Data.(type) {
		case *ast.EBinary:
			if e.Op == ast.BinOpAssign && findRestBindings(e.Left) {
				found = true
			}
		case *ast.EArray:
			for _, item := range e.Items {
				if findRestBindings(item) {
					found = true
				}
			}
		case *ast.EObject:
			for _, property := range e.Properties {
				if property.Kind == ast.PropertySpread || findRestBindings(property.ValueOrNil) {
					found = true
				}
			}
		}
		if found {
			containsRestBinding[expr.Data] = true
		}
		return found
	}
	findRestBindings(rootExpr)
	if len(containsRestBinding) == 0 {
		return nil, false
	}

	// If there is at least one rest binding, lower the whole expression
	var visit func(ast.Expr, ast.Expr, []func() ast.Expr)

	captureIntoRef := func(expr ast.Expr) ast.Ref {
		ref := p.generateTempRef(declare, "")
		assign(ast.Expr{Loc: expr.Loc, Data: &ast.EIdentifier{Ref: ref}}, expr)
		p.recordUsage(ref)
		return ref
	}

	lowerObjectRestPattern := func(
		before []ast.Property,
		binding ast.Expr,
		init ast.Expr,
		capturedKeys []func() ast.Expr,
		isSingleLine bool,
	) {
		// If there are properties before this one, store the initializer in a
		// temporary so we can reference it multiple times, then create a new
		// destructuring assignment for these properties
		if len(before) > 0 {
			// "let {a, ...b} = c"
			ref := captureIntoRef(init)
			assign(ast.Expr{Loc: before[0].Key.Loc, Data: &ast.EObject{Properties: before, IsSingleLine: isSingleLine}},
				ast.Expr{Loc: init.Loc, Data: &ast.EIdentifier{Ref: ref}})
			init = ast.Expr{Loc: init.Loc, Data: &ast.EIdentifier{Ref: ref}}
			p.recordUsage(ref)
			p.recordUsage(ref)
		}

		// Call "__objRest" to clone the initializer without the keys for previous
		// properties, then assign the result to the binding for the rest pattern
		keysToExclude := make([]ast.Expr, len(capturedKeys))
		for i, capturedKey := range capturedKeys {
			keysToExclude[i] = capturedKey()
		}
		assign(binding, p.callRuntime(binding.Loc, "__objRest", []ast.Expr{init,
			{Loc: binding.Loc, Data: &ast.EArray{Items: keysToExclude, IsSingleLine: isSingleLine}}}))
	}

	splitArrayPattern := func(
		before []ast.Expr,
		split ast.Expr,
		after []ast.Expr,
		init ast.Expr,
		isSingleLine bool,
	) {
		// If this has a default value, skip the value to target the binding
		binding := &split
		if binary, ok := binding.Data.(*ast.EBinary); ok && binary.Op == ast.BinOpAssign {
			binding = &binary.Left
		}

		// Swap the binding with a temporary
		splitRef := p.generateTempRef(declare, "")
		deferredBinding := *binding
		binding.Data = &ast.EIdentifier{Ref: splitRef}
		items := append(before, split)

		// If there are any items left over, defer them until later too
		var tailExpr ast.Expr
		var tailInit ast.Expr
		if len(after) > 0 {
			tailRef := p.generateTempRef(declare, "")
			loc := after[0].Loc
			tailExpr = ast.Expr{Loc: loc, Data: &ast.EArray{Items: after, IsSingleLine: isSingleLine}}
			tailInit = ast.Expr{Loc: loc, Data: &ast.EIdentifier{Ref: tailRef}}
			items = append(items, ast.Expr{Loc: loc, Data: &ast.ESpread{Value: ast.Expr{Loc: loc, Data: &ast.EIdentifier{Ref: tailRef}}}})
			p.recordUsage(tailRef)
			p.recordUsage(tailRef)
		}

		// The original destructuring assignment must come first
		assign(ast.Expr{Loc: split.Loc, Data: &ast.EArray{Items: items, IsSingleLine: isSingleLine}}, init)

		// Then the deferred split is evaluated
		visit(deferredBinding, ast.Expr{Loc: split.Loc, Data: &ast.EIdentifier{Ref: splitRef}}, nil)
		p.recordUsage(splitRef)

		// Then anything after the split
		if len(after) > 0 {
			visit(tailExpr, tailInit, nil)
		}
	}

	splitObjectPattern := func(
		upToSplit []ast.Property,
		afterSplit []ast.Property,
		init ast.Expr,
		capturedKeys []func() ast.Expr,
		isSingleLine bool,
	) {
		// If there are properties after the split, store the initializer in a
		// temporary so we can reference it multiple times
		var afterSplitInit ast.Expr
		if len(afterSplit) > 0 {
			ref := captureIntoRef(init)
			init = ast.Expr{Loc: init.Loc, Data: &ast.EIdentifier{Ref: ref}}
			afterSplitInit = ast.Expr{Loc: init.Loc, Data: &ast.EIdentifier{Ref: ref}}
		}

		split := &upToSplit[len(upToSplit)-1]
		binding := &split.ValueOrNil

		// Swap the binding with a temporary
		splitRef := p.generateTempRef(declare, "")
		deferredBinding := *binding
		binding.Data = &ast.EIdentifier{Ref: splitRef}
		p.recordUsage(splitRef)

		// Use a destructuring assignment to unpack everything up to and including
		// the split point
		assign(ast.Expr{Loc: binding.Loc, Data: &ast.EObject{Properties: upToSplit, IsSingleLine: isSingleLine}}, init)

		// Handle any nested rest binding patterns inside the split point
		visit(deferredBinding, ast.Expr{Loc: binding.Loc, Data: &ast.EIdentifier{Ref: splitRef}}, nil)
		p.recordUsage(splitRef)

		// Then continue on to any properties after the split
		if len(afterSplit) > 0 {
			visit(ast.Expr{Loc: binding.Loc, Data: &ast.EObject{
				Properties:   afterSplit,
				IsSingleLine: isSingleLine,
			}}, afterSplitInit, capturedKeys)
		}
	}

	// This takes an expression representing a binding pattern as input and
	// returns that binding pattern with any object rest patterns stripped out.
	// The object rest patterns are lowered and appended to "exprChain" along
	// with any child binding patterns that came after the binding pattern
	// containing the object rest pattern.
	//
	// This transform must be very careful to preserve the exact evaluation
	// order of all assignments, default values, and computed property keys.
	//
	// Unlike the Babel and TypeScript compilers, this transform does not
	// lower binding patterns other than object rest patterns. For example,
	// array spread patterns are preserved.
	//
	// Certain patterns such as "{a: {...a}, b: {...b}, ...c}" may need to be
	// split multiple times. In this case the "capturedKeys" argument allows
	// the visitor to pass on captured keys to the tail-recursive call that
	// handles the properties after the split.
	visit = func(expr ast.Expr, init ast.Expr, capturedKeys []func() ast.Expr) {
		switch e := expr.Data.(type) {
		case *ast.EArray:
			// Split on the first binding with a nested rest binding pattern
			for i, item := range e.Items {
				// "let [a, {...b}, c] = d"
				if containsRestBinding[item.Data] {
					splitArrayPattern(e.Items[:i], item, append([]ast.Expr{}, e.Items[i+1:]...), init, e.IsSingleLine)
					return
				}
			}

		case *ast.EObject:
			last := len(e.Properties) - 1
			endsWithRestBinding := last >= 0 && e.Properties[last].Kind == ast.PropertySpread

			// Split on the first binding with a nested rest binding pattern
			for i := range e.Properties {
				property := &e.Properties[i]

				// "let {a, ...b} = c"
				if property.Kind == ast.PropertySpread {
					lowerObjectRestPattern(e.Properties[:i], property.ValueOrNil, init, capturedKeys, e.IsSingleLine)
					return
				}

				// Save a copy of this key so the rest binding can exclude it
				if endsWithRestBinding {
					key, capturedKey := p.captureKeyForObjectRest(property.Key)
					property.Key = key
					capturedKeys = append(capturedKeys, capturedKey)
				}

				// "let {a: {...b}, c} = d"
				if containsRestBinding[property.ValueOrNil.Data] {
					splitObjectPattern(e.Properties[:i+1], e.Properties[i+1:], init, capturedKeys, e.IsSingleLine)
					return
				}
			}
		}

		assign(expr, init)
	}

	// Capture and return the value of the initializer if this is an assignment
	// expression and the return value is used:
	//
	//   // Input:
	//   console.log({...x} = x);
	//
	//   // Output:
	//   var _a;
	//   console.log((x = __objRest(_a = x, []), _a));
	//
	// This isn't necessary if the return value is unused:
	//
	//   // Input:
	//   ({...x} = x);
	//
	//   // Output:
	//   x = __objRest(x, []);
	//
	if mode == objRestMustReturnInitExpr {
		initFunc, initWrapFunc := p.captureValueWithPossibleSideEffects(rootInit.Loc, 2, rootInit, valueCouldBeMutated)
		rootInit = initFunc()
		wrapFunc = func(expr ast.Expr) ast.Expr {
			return initWrapFunc(ast.JoinWithComma(expr, initFunc()))
		}
	}

	visit(rootExpr, rootInit, nil)
	return wrapFunc, true
}

// Save a copy of the key for the call to "__objRest" later on. Certain
// expressions can be converted to keys more efficiently than others.
func (p *parser) captureKeyForObjectRest(originalKey ast.Expr) (finalKey ast.Expr, capturedKey func() ast.Expr) {
	loc := originalKey.Loc
	finalKey = originalKey

	switch k := originalKey.Data.(type) {
	case *ast.EString:
		capturedKey = func() ast.Expr { return ast.Expr{Loc: loc, Data: &ast.EString{Value: k.Value}} }

	case *ast.ENumber:
		// Emit it as the number plus a string (i.e. call toString() on it).
		// It's important to do it this way instead of trying to print the
		// float as a string because Go's floating-point printer doesn't
		// behave exactly the same as JavaScript and if they are different,
		// the generated code will be wrong.
		capturedKey = func() ast.Expr {
			return ast.Expr{Loc: loc, Data: &ast.EBinary{
				Op:    ast.BinOpAdd,
				Left:  ast.Expr{Loc: loc, Data: &ast.ENumber{Value: k.Value}},
				Right: ast.Expr{Loc: loc, Data: &ast.EString{}},
			}}
		}

	case *ast.EIdentifier:
		capturedKey = func() ast.Expr {
			p.recordUsage(k.Ref)
			return p.callRuntime(loc, "__restKey", []ast.Expr{{Loc: loc, Data: &ast.EIdentifier{Ref: k.Ref}}})
		}

	default:
		// If it's an arbitrary expression, it probably has a side effect.
		// Stash it in a temporary reference so we don't evaluate it twice.
		tempRef := p.generateTempRef(tempRefNeedsDeclare, "")
		finalKey = ast.Assign(ast.Expr{Loc: loc, Data: &ast.EIdentifier{Ref: tempRef}}, originalKey)
		capturedKey = func() ast.Expr {
			p.recordUsage(tempRef)
			return p.callRuntime(loc, "__restKey", []ast.Expr{{Loc: loc, Data: &ast.EIdentifier{Ref: tempRef}}})
		}
	}

	return
}

type classLoweringInfo struct {
	useDefineForClassFields bool
	avoidTDZ                bool
	lowerAllInstanceFields  bool
	lowerAllStaticFields    bool
}

func (p *parser) computeClassLoweringInfo(class *ast.Class) (result classLoweringInfo) {
	// TypeScript has legacy behavior that uses assignment semantics instead of
	// define semantics for class fields by default. This happened before class
	// fields were added to JavaScript, but then TC39 decided to go with define
	// semantics for class fields instead, leaving TypeScript to deal with the
	// incorrect assignment semantics. This behaves differently if the base class
	// has a setter with the same name.
	result.useDefineForClassFields = p.options.useDefineForClassFields != config.False

	// Safari workaround: Automatically avoid TDZ issues when bundling
	result.avoidTDZ = p.options.mode == config.ModeBundle && p.currentScope.Parent == nil

	// Conservatively lower fields of a given type (instance or static) when any
	// member of that type needs to be lowered. This must be done to preserve
	// evaluation order. For example:
	//
	//   class Foo {
	//     #foo = 123
	//     bar = this.#foo
	//   }
	//
	// It would be bad if we transformed that into something like this:
	//
	//   var _foo;
	//   class Foo {
	//     constructor() {
	//       _foo.set(this, 123);
	//     }
	//     bar = __privateGet(this, _foo);
	//   }
	//   _foo = new WeakMap();
	//
	// That evaluates "bar" then "foo" instead of "foo" then "bar" like the
	// original code. We need to do this instead:
	//
	//   var _foo;
	//   class Foo {
	//     constructor() {
	//       _foo.set(this, 123);
	//       __publicField(this, "bar", __privateGet(this, _foo));
	//     }
	//   }
	//   _foo = new WeakMap();
	//
	for _, prop := range class.Properties {
		if prop.Kind == ast.PropertyClassStaticBlock {
			if p.options.unsupportedJSFeatures.Has(compat.ClassStaticBlocks) && len(prop.ClassStaticBlock.Stmts) > 0 {
				result.lowerAllStaticFields = true
			}
			continue
		}

		if private, ok := prop.Key.Data.(*ast.EPrivateIdentifier); ok {
			if prop.IsStatic {
				if p.privateSymbolNeedsToBeLowered(private) {
					result.lowerAllStaticFields = true
				}

				// Be conservative and always lower static fields when we're doing TDZ-
				// avoidance if the class's shadowing symbol is referenced at all (i.e.
				// the class name within the class body, which can be referenced by name
				// or by "this" in a static initializer). We can't transform this:
				//
				//   class Foo {
				//     static #foo = new Foo();
				//   }
				//
				// into this:
				//
				//   var Foo = class {
				//     static #foo = new Foo();
				//   };
				//
				// since "new Foo" will crash. We need to lower this static field to avoid
				// crashing due to an uninitialized binding.
				if result.avoidTDZ {
					// Note that due to esbuild's single-pass design where private fields
					// are lowered as they are resolved, we must decide whether to lower
					// these private fields before we enter the class body. We can't wait
					// until we've scanned the class body and know if the shadowing symbol
					// is used or not before we decide, because if "#foo" does need to be
					// lowered, references to "#foo" inside the class body weren't lowered.
					// So we just unconditionally do this instead.
					result.lowerAllStaticFields = true
				}
			} else {
				if p.privateSymbolNeedsToBeLowered(private) {
					result.lowerAllInstanceFields = true

					// We can't transform this:
					//
					//   class Foo {
					//     #foo = 123
					//     static bar = new Foo().#foo
					//   }
					//
					// into this:
					//
					//   var _foo;
					//   const _Foo = class {
					//     constructor() {
					//       _foo.set(this, 123);
					//     }
					//     static bar = __privateGet(new _Foo(), _foo);
					//   };
					//   let Foo = _Foo;
					//   _foo = new WeakMap();
					//
					// because "_Foo" won't be initialized in the initializer for "bar".
					// So we currently lower all static fields in this case too. This
					// isn't great and it would be good to find a way to avoid this.
					// The shadowing symbol substitution mechanism should probably be
					// rethought.
					result.lowerAllStaticFields = true
				}
			}
			continue
		}

		// This doesn't come before the private member check above because
		// unsupported private methods must also trigger field lowering:
		//
		//   class Foo {
		//     bar = this.#foo()
		//     #foo() {}
		//   }
		//
		// It would be bad if we transformed that to something like this:
		//
		//   var _foo, foo_fn;
		//   class Foo {
		//     constructor() {
		//       _foo.add(this);
		//     }
		//     bar = __privateMethod(this, _foo, foo_fn).call(this);
		//   }
		//   _foo = new WeakSet();
		//   foo_fn = function() {
		//   };
		//
		// In that case the initializer of "bar" would fail to call "#foo" because
		// it's only added to the instance in the body of the constructor.
		if prop.IsMethod {
			continue
		}

		if prop.IsStatic {
			// Static fields must be lowered if the target doesn't support them
			if p.options.unsupportedJSFeatures.Has(compat.ClassStaticField) {
				result.lowerAllStaticFields = true
			}

			// Convert static fields to assignment statements if the TypeScript
			// setting for this is enabled. I don't think this matters for private
			// fields because there's no way for this to call a setter in the base
			// class, so this isn't done for private fields.
			if p.options.ts.Parse && !result.useDefineForClassFields {
				result.lowerAllStaticFields = true
			}

			// Be conservative and always lower static fields when we're doing TDZ-
			// avoidance. We can't transform this:
			//
			//   class Foo {
			//     static foo = new Foo();
			//   }
			//
			// into this:
			//
			//   var Foo = class {
			//     static foo = new Foo();
			//   };
			//
			// since "new Foo" will crash. We need to lower this static field to avoid
			// crashing due to an uninitialized binding.
			if result.avoidTDZ {
				result.lowerAllStaticFields = true
			}
		} else {
			// Instance fields must be lowered if the target doesn't support them
			if p.options.unsupportedJSFeatures.Has(compat.ClassField) {
				result.lowerAllInstanceFields = true
			}

			// Convert instance fields to assignment statements if the TypeScript
			// setting for this is enabled. I don't think this matters for private
			// fields because there's no way for this to call a setter in the base
			// class, so this isn't done for private fields.
			if p.options.ts.Parse && !result.useDefineForClassFields {
				result.lowerAllInstanceFields = true
			}
		}
	}

	return
}

// Lower class fields for environments that don't support them. This either
// takes a statement or an expression.
func (p *parser) lowerClass(stmt ast.Stmt, expr ast.Expr, shadowRef ast.Ref) ([]ast.Stmt, ast.Expr) {
	type classKind uint8
	const (
		classKindExpr classKind = iota
		classKindStmt
		classKindExportStmt
		classKindExportDefaultStmt
	)

	// Unpack the class from the statement or expression
	var kind classKind
	var class *ast.Class
	var classLoc logger.Loc
	var defaultName ast.LocRef
	var nameToKeep string
	if stmt.Data == nil {
		e, _ := expr.Data.(*ast.EClass)
		class = &e.Class
		kind = classKindExpr
		if class.Name != nil {
			symbol := &p.symbols[class.Name.Ref.InnerIndex]
			nameToKeep = symbol.OriginalName

			// The shadowing name inside the class expression should be the same as
			// the class expression name itself
			if shadowRef != ast.InvalidRef {
				p.mergeSymbols(shadowRef, class.Name.Ref)
			}

			// Remove unused class names when minifying. Check this after we merge in
			// the shadowing name above since that will adjust the use count.
			if p.options.mangleSyntax && symbol.UseCountEstimate == 0 {
				class.Name = nil
			}
		}
	} else if s, ok := stmt.Data.(*ast.SClass); ok {
		class = &s.Class
		if s.IsExport {
			kind = classKindExportStmt
		} else {
			kind = classKindStmt
		}
		nameToKeep = p.symbols[class.Name.Ref.InnerIndex].OriginalName
	} else {
		s, _ := stmt.Data.(*ast.SExportDefault)
		s2, _ := s.Value.Data.(*ast.SClass)
		class = &s2.Class
		defaultName = s.DefaultName
		kind = classKindExportDefaultStmt
		if class.Name != nil {
			nameToKeep = p.symbols[class.Name.Ref.InnerIndex].OriginalName
		} else {
			nameToKeep = "default"
		}
	}
	if stmt.Data == nil {
		classLoc = expr.Loc
	} else {
		classLoc = stmt.Loc
	}

	var ctor *ast.EFunction
	var parameterFields []ast.Stmt
	var instanceMembers []ast.Stmt
	var instancePrivateMethods []ast.Stmt
	end := 0

	// These expressions are generated after the class body, in this order
	var computedPropertyCache ast.Expr
	var privateMembers []ast.Expr
	var staticMembers []ast.Expr
	var staticPrivateMethods []ast.Expr
	var instanceDecorators []ast.Expr
	var staticDecorators []ast.Expr

	// These are only for class expressions that need to be captured
	var nameFunc func() ast.Expr
	var wrapFunc func(ast.Expr) ast.Expr
	didCaptureClassExpr := false

	// Class statements can be missing a name if they are in an
	// "export default" statement:
	//
	//   export default class {
	//     static foo = 123
	//   }
	//
	nameFunc = func() ast.Expr {
		if kind == classKindExpr {
			// If this is a class expression, capture and store it. We have to
			// do this even if it has a name since the name isn't exposed
			// outside the class body.
			classExpr := &ast.EClass{Class: *class}
			class = &classExpr.Class
			nameFunc, wrapFunc = p.captureValueWithPossibleSideEffects(classLoc, 2, ast.Expr{Loc: classLoc, Data: classExpr}, valueDefinitelyNotMutated)
			expr = nameFunc()
			didCaptureClassExpr = true
			name := nameFunc()

			// If we're storing the class expression in a variable, remove the class
			// name and rewrite all references to the class name with references to
			// the temporary variable holding the class expression. This ensures that
			// references to the class expression by name in any expressions that end
			// up being pulled outside of the class body still work. For example:
			//
			//   let Bar = class Foo {
			//     static foo = 123
			//     static bar = Foo.foo
			//   }
			//
			// This might be converted into the following:
			//
			//   var _a;
			//   let Bar = (_a = class {
			//   }, _a.foo = 123, _a.bar = _a.foo, _a);
			//
			if class.Name != nil {
				p.mergeSymbols(class.Name.Ref, name.Data.(*ast.EIdentifier).Ref)
				class.Name = nil
			}

			return name
		} else {
			if class.Name == nil {
				if kind == classKindExportDefaultStmt {
					class.Name = &defaultName
				} else {
					class.Name = &ast.LocRef{Loc: classLoc, Ref: p.generateTempRef(tempRefNoDeclare, "")}
				}
			}
			p.recordUsage(class.Name.Ref)
			return ast.Expr{Loc: classLoc, Data: &ast.EIdentifier{Ref: class.Name.Ref}}
		}
	}

	classLoweringInfo := p.computeClassLoweringInfo(class)

	for _, prop := range class.Properties {
		if prop.Kind == ast.PropertyClassStaticBlock {
			if p.options.unsupportedJSFeatures.Has(compat.ClassStaticBlocks) {
				if block := *prop.ClassStaticBlock; len(block.Stmts) > 0 {
					staticMembers = append(staticMembers, ast.Expr{Loc: block.Loc, Data: &ast.ECall{
						Target: ast.Expr{Loc: block.Loc, Data: &ast.EArrow{Body: ast.FnBody{
							Stmts: block.Stmts,
						}}},
					}})
				}
				continue
			}

			// Keep this property
			class.Properties[end] = prop
			end++
			continue
		}

		// Merge parameter decorators with method decorators
		if p.options.ts.Parse && prop.IsMethod {
			if fn, ok := prop.ValueOrNil.Data.(*ast.EFunction); ok {
				isConstructor := false
				if key, ok := prop.Key.Data.(*ast.EString); ok {
					isConstructor = lexer.UTF16EqualsString(key.Value, "constructor")
				}
				for i, arg := range fn.Fn.Args {
					for _, decorator := range arg.TSDecorators {
						// Generate a call to "__decorateParam()" for this parameter decorator
						var decorators *[]ast.Expr = &prop.TSDecorators
						if isConstructor {
							decorators = &class.TSDecorators
						}
						*decorators = append(*decorators,
							p.callRuntime(decorator.Loc, "__decorateParam", []ast.Expr{
								{Loc: decorator.Loc, Data: &ast.ENumber{Value: float64(i)}},
								decorator,
							}),
						)
					}
				}
			}
		}

		// The TypeScript class field transform requires removing fields without
		// initializers. If the field is removed, then we only need the key for
		// its side effects and we don't need a temporary reference for the key.
		// However, the TypeScript compiler doesn't remove the field when doing
		// strict class field initialization, so we shouldn't either.
		private, _ := prop.Key.Data.(*ast.EPrivateIdentifier)
		mustLowerPrivate := private != nil && p.privateSymbolNeedsToBeLowered(private)
		shouldOmitFieldInitializer := p.options.ts.Parse && !prop.IsMethod && prop.InitializerOrNil.Data == nil &&
			!classLoweringInfo.useDefineForClassFields && !mustLowerPrivate

		// Class fields must be lowered if the environment doesn't support them
		mustLowerField := false
		if !prop.IsMethod {
			if prop.IsStatic {
				mustLowerField = classLoweringInfo.lowerAllStaticFields
			} else {
				mustLowerField = classLoweringInfo.lowerAllInstanceFields
			}
		}

		// If the field uses the TypeScript "declare" keyword, just omit it entirely.
		// However, we must still keep any side-effects in the computed value and/or
		// in the decorators.
		if prop.Kind == ast.PropertyDeclare && prop.ValueOrNil.Data == nil {
			mustLowerField = true
			shouldOmitFieldInitializer = true
		}

		// Make sure the order of computed property keys doesn't change. These
		// expressions have side effects and must be evaluated in order.
		keyExprNoSideEffects := prop.Key
		if prop.IsComputed && (len(prop.TSDecorators) > 0 ||
			mustLowerField || computedPropertyCache.Data != nil) {
			needsKey := true
			if len(prop.TSDecorators) == 0 && (prop.IsMethod || shouldOmitFieldInitializer || !mustLowerField) {
				needsKey = false
			}

			if !needsKey {
				// Just evaluate the key for its side effects
				computedPropertyCache = ast.JoinWithComma(computedPropertyCache, prop.Key)
			} else {
				// Store the key in a temporary so we can assign to it later
				ref := p.generateTempRef(tempRefNeedsDeclare, "")
				computedPropertyCache = ast.JoinWithComma(computedPropertyCache,
					ast.Assign(ast.Expr{Loc: prop.Key.Loc, Data: &ast.EIdentifier{Ref: ref}}, prop.Key))
				prop.Key = ast.Expr{Loc: prop.Key.Loc, Data: &ast.EIdentifier{Ref: ref}}
				keyExprNoSideEffects = prop.Key
			}

			// If this is a computed method, the property value will be used
			// immediately. In this case we inline all computed properties so far to
			// make sure all computed properties before this one are evaluated first.
			if !mustLowerField {
				prop.Key = computedPropertyCache
				computedPropertyCache = ast.Expr{}
			}
		}

		// Handle decorators
		if p.options.ts.Parse {
			// Generate a single call to "__decorateClass()" for this property
			if len(prop.TSDecorators) > 0 {
				loc := prop.Key.Loc

				// Clone the key for the property descriptor
				var descriptorKey ast.Expr
				switch k := keyExprNoSideEffects.Data.(type) {
				case *ast.ENumber:
					descriptorKey = ast.Expr{Loc: loc, Data: &ast.ENumber{Value: k.Value}}
				case *ast.EString:
					descriptorKey = ast.Expr{Loc: loc, Data: &ast.EString{Value: k.Value}}
				case *ast.EIdentifier:
					descriptorKey = ast.Expr{Loc: loc, Data: &ast.EIdentifier{Ref: k.Ref}}
				default:
					panic("Internal error")
				}

				// This code tells "__decorateClass()" if the descriptor should be undefined
				descriptorKind := float64(1)
				if !prop.IsMethod {
					descriptorKind = 2
				}

				// Instance properties use the prototype, static properties use the class
				var target ast.Expr
				if prop.IsStatic {
					target = nameFunc()
				} else {
					target = ast.Expr{Loc: loc, Data: &ast.EDot{Target: nameFunc(), Name: "prototype", NameLoc: loc}}
				}

				decorator := p.callRuntime(loc, "__decorateClass", []ast.Expr{
					{Loc: loc, Data: &ast.EArray{Items: prop.TSDecorators}},
					target,
					descriptorKey,
					{Loc: loc, Data: &ast.ENumber{Value: descriptorKind}},
				})

				// Static decorators are grouped after instance decorators
				if prop.IsStatic {
					staticDecorators = append(staticDecorators, decorator)
				} else {
					instanceDecorators = append(instanceDecorators, decorator)
				}
			}
		}

		// Handle lowering of instance and static fields. Move their initializers
		// from the class body to either the constructor (instance fields) or after
		// the class (static fields).
		if !prop.IsMethod && mustLowerField {
			// The TypeScript compiler doesn't follow the JavaScript spec for
			// uninitialized fields. They are supposed to be set to undefined but the
			// TypeScript compiler just omits them entirely.
			if !shouldOmitFieldInitializer {
				loc := prop.Key.Loc

				// Determine where to store the field
				var target ast.Expr
				if prop.IsStatic {
					target = nameFunc()
				} else {
					target = ast.Expr{Loc: loc, Data: ast.EThisShared}
				}

				// Generate the assignment initializer
				var init ast.Expr
				if prop.InitializerOrNil.Data != nil {
					init = prop.InitializerOrNil
				} else {
					init = ast.Expr{Loc: loc, Data: ast.EUndefinedShared}
				}

				// Generate the assignment target
				var memberExpr ast.Expr
				if mustLowerPrivate {
					// Generate a new symbol for this private field
					ref := p.generateTempRef(tempRefNeedsDeclare, "_"+p.symbols[private.Ref.InnerIndex].OriginalName[1:])
					p.symbols[private.Ref.InnerIndex].Link = ref

					// Initialize the private field to a new WeakMap
					if p.weakMapRef == ast.InvalidRef {
						p.weakMapRef = p.newSymbol(ast.SymbolUnbound, "WeakMap")
						p.moduleScope.Generated = append(p.moduleScope.Generated, p.weakMapRef)
					}
					privateMembers = append(privateMembers, ast.Assign(
						ast.Expr{Loc: loc, Data: &ast.EIdentifier{Ref: ref}},
						ast.Expr{Loc: loc, Data: &ast.ENew{Target: ast.Expr{Loc: loc, Data: &ast.EIdentifier{Ref: p.weakMapRef}}}},
					))
					p.recordUsage(ref)

					// Add every newly-constructed instance into this map
					memberExpr = p.callRuntime(loc, "__privateAdd", []ast.Expr{
						target,
						{Loc: loc, Data: &ast.EIdentifier{Ref: ref}},
						init,
					})
					p.recordUsage(ref)
				} else if private == nil && classLoweringInfo.useDefineForClassFields {
					if _, ok := init.Data.(*ast.EUndefined); ok {
						memberExpr = p.callRuntime(loc, "__publicField", []ast.Expr{target, prop.Key})
					} else {
						memberExpr = p.callRuntime(loc, "__publicField", []ast.Expr{target, prop.Key, init})
					}
				} else {
					if key, ok := prop.Key.Data.(*ast.EString); ok && !prop.IsComputed {
						target = ast.Expr{Loc: loc, Data: &ast.EDot{
							Target:  target,
							Name:    lexer.UTF16ToString(key.Value),
							NameLoc: loc,
						}}
					} else {
						target = ast.Expr{Loc: loc, Data: &ast.EIndex{
							Target: target,
							Index:  prop.Key,
						}}
					}

					memberExpr = ast.Assign(target, init)
				}

				if prop.IsStatic {
					// Move this property to an assignment after the class ends
					staticMembers = append(staticMembers, memberExpr)
				} else {
					// Move this property to an assignment inside the class constructor
					instanceMembers = append(instanceMembers, ast.Stmt{Loc: loc, Data: &ast.SExpr{Value: memberExpr}})
				}
			}

			if private == nil || mustLowerPrivate {
				// Remove the field from the class body
				continue
			}

			// Keep the private field but remove the initializer
			prop.InitializerOrNil = ast.Expr{}
		}

		if prop.IsMethod {
			if mustLowerPrivate {
				loc := prop.Key.Loc

				// Don't generate a symbol for a getter/setter pair twice
				if p.symbols[private.Ref.InnerIndex].Link == ast.InvalidRef {
					// Generate a new symbol for this private method
					ref := p.generateTempRef(tempRefNeedsDeclare, "_"+p.symbols[private.Ref.InnerIndex].OriginalName[1:])
					p.symbols[private.Ref.InnerIndex].Link = ref

					// Initialize the private method to a new WeakSet
					if p.weakSetRef == ast.InvalidRef {
						p.weakSetRef = p.newSymbol(ast.SymbolUnbound, "WeakSet")
						p.moduleScope.Generated = append(p.moduleScope.Generated, p.weakSetRef)
					}
					privateMembers = append(privateMembers, ast.Assign(
						ast.Expr{Loc: loc, Data: &ast.EIdentifier{Ref: ref}},
						ast.Expr{Loc: loc, Data: &ast.ENew{Target: ast.Expr{Loc: loc, Data: &ast.EIdentifier{Ref: p.weakSetRef}}}},
					))
					p.recordUsage(ref)

					// Determine where to store the private method
					var target ast.Expr
					if prop.IsStatic {
						target = nameFunc()
					} else {
						target = ast.Expr{Loc: loc, Data: ast.EThisShared}
					}

					// Add every newly-constructed instance into this map
					methodExpr := p.callRuntime(loc, "__privateAdd", []ast.Expr{
						target,
						{Loc: loc, Data: &ast.EIdentifier{Ref: ref}},
					})
					p.recordUsage(ref)

					// Make sure that adding to the map happens before any field
					// initializers to handle cases like this:
					//
					//   class A {
					//     pub = this.#priv;
					//     #priv() {}
					//   }
					//
					if prop.IsStatic {
						// Move this property to an assignment after the class ends
						staticPrivateMethods = append(staticPrivateMethods, methodExpr)
					} else {
						// Move this property to an assignment inside the class constructor
						instancePrivateMethods = append(instancePrivateMethods, ast.Stmt{Loc: loc, Data: &ast.SExpr{Value: methodExpr}})
					}
				}

				// Move the method definition outside the class body
				methodRef := p.generateTempRef(tempRefNeedsDeclare, "_")
				if prop.Kind == ast.PropertySet {
					p.symbols[methodRef.InnerIndex].Link = p.privateSetters[private.Ref]
				} else {
					p.symbols[methodRef.InnerIndex].Link = p.privateGetters[private.Ref]
				}
				privateMembers = append(privateMembers, ast.Assign(
					ast.Expr{Loc: loc, Data: &ast.EIdentifier{Ref: methodRef}},
					prop.ValueOrNil,
				))
				continue
			} else if key, ok := prop.Key.Data.(*ast.EString); ok && lexer.UTF16EqualsString(key.Value, "constructor") {
				if fn, ok := prop.ValueOrNil.Data.(*ast.EFunction); ok {
					// Remember where the constructor is for later
					ctor = fn

					// Initialize TypeScript constructor parameter fields
					if p.options.ts.Parse {
						for _, arg := range ctor.Fn.Args {
							if arg.IsTypeScriptCtorField {
								if id, ok := arg.Binding.Data.(*ast.BIdentifier); ok {
									parameterFields = append(parameterFields, ast.AssignStmt(
										ast.Expr{Loc: arg.Binding.Loc, Data: &ast.EDot{
											Target:  ast.Expr{Loc: arg.Binding.Loc, Data: ast.EThisShared},
											Name:    p.symbols[id.Ref.InnerIndex].OriginalName,
											NameLoc: arg.Binding.Loc,
										}},
										ast.Expr{Loc: arg.Binding.Loc, Data: &ast.EIdentifier{Ref: id.Ref}},
									))
								}
							}
						}
					}
				}
			}
		}

		// Keep this property
		class.Properties[end] = prop
		end++
	}

	// Finish the filtering operation
	class.Properties = class.Properties[:end]

	// Insert instance field initializers into the constructor
	if len(parameterFields) > 0 || len(instancePrivateMethods) > 0 || len(instanceMembers) > 0 {
		// Create a constructor if one doesn't already exist
		if ctor == nil {
			ctor = &ast.EFunction{}

			// Append it to the list to reuse existing allocation space
			class.Properties = append(class.Properties, ast.Property{
				IsMethod:   true,
				Key:        ast.Expr{Loc: classLoc, Data: &ast.EString{Value: lexer.StringToUTF16("constructor")}},
				ValueOrNil: ast.Expr{Loc: classLoc, Data: ctor},
			})

			// Make sure the constructor has a super() call if needed
			if class.ExtendsOrNil.Data != nil {
				argumentsRef := p.newSymbol(ast.SymbolUnbound, "arguments")
				p.currentScope.Generated = append(p.currentScope.Generated, argumentsRef)
				ctor.Fn.Body.Stmts = append(ctor.Fn.Body.Stmts, ast.Stmt{Loc: classLoc, Data: &ast.SExpr{Value: ast.Expr{Loc: classLoc, Data: &ast.ECall{
					Target: ast.Expr{Loc: classLoc, Data: ast.ESuperShared},
					Args:   []ast.Expr{{Loc: classLoc, Data: &ast.ESpread{Value: ast.Expr{Loc: classLoc, Data: &ast.EIdentifier{Ref: argumentsRef}}}}},
				}}}})
			}
		}

		// Insert the instance field initializers after the super call if there is one
		stmtsFrom := ctor.Fn.Body.Stmts
		stmtsTo := []ast.Stmt{}
		for i, stmt := range stmtsFrom {
			if ast.IsSuperCall(stmt) {
				stmtsTo = append(stmtsTo, stmtsFrom[0:i+1]...)
				stmtsFrom = stmtsFrom[i+1:]
				break
			}
		}
		stmtsTo = append(stmtsTo, parameterFields...)
		stmtsTo = append(stmtsTo, instancePrivateMethods...)
		stmtsTo = append(stmtsTo, instanceMembers...)
		ctor.Fn.Body.Stmts = append(stmtsTo, stmtsFrom...)

		// Sort the constructor first to match the TypeScript compiler's output
		for i := 0; i < len(class.Properties); i++ {
			if class.Properties[i].ValueOrNil.Data == ctor {
				ctorProp := class.Properties[i]
				for j := i; j > 0; j-- {
					class.Properties[j] = class.Properties[j-1]
				}
				class.Properties[0] = ctorProp
				break
			}
		}
	}

	// Pack the class back into an expression. We don't need to handle TypeScript
	// decorators for class expressions because TypeScript doesn't support them.
	if kind == classKindExpr {
		// Calling "nameFunc" will replace "expr", so make sure to do that first
		// before joining "expr" with any other expressions
		var nameToJoin ast.Expr
		if didCaptureClassExpr || computedPropertyCache.Data != nil ||
			len(privateMembers) > 0 || len(staticPrivateMethods) > 0 || len(staticMembers) > 0 {
			nameToJoin = nameFunc()
		}

		// Optionally preserve the name
		if p.options.keepNames && nameToKeep != "" {
			expr = p.keepExprSymbolName(expr, nameToKeep)
		}

		// Then join "expr" with any other expressions that apply
		if computedPropertyCache.Data != nil {
			expr = ast.JoinWithComma(expr, computedPropertyCache)
		}
		for _, value := range privateMembers {
			expr = ast.JoinWithComma(expr, value)
		}
		for _, value := range staticPrivateMethods {
			expr = ast.JoinWithComma(expr, value)
		}
		for _, value := range staticMembers {
			expr = ast.JoinWithComma(expr, value)
		}

		// Finally join "expr" with the variable that holds the class object
		if nameToJoin.Data != nil {
			expr = ast.JoinWithComma(expr, nameToJoin)
		}
		if wrapFunc != nil {
			expr = wrapFunc(expr)
		}
		return nil, expr
	}

	// If this is true, we have removed some code from the class body that could
	// potentially contain an expression that captures the shadowing class name.
	// This could lead to incorrect behavior if the class is later re-assigned,
	// since the removed code would no longer be in the shadowing scope.
	hasPotentialShadowCaptureEscape := shadowRef != ast.InvalidRef &&
		(computedPropertyCache.Data != nil ||
			len(privateMembers) > 0 ||
			len(staticPrivateMethods) > 0 ||
			len(staticMembers) > 0 ||
			len(instanceDecorators) > 0 ||
			len(staticDecorators) > 0 ||
			len(class.TSDecorators) > 0)

	// Optionally preserve the name
	var keepNameStmt ast.Stmt
	if p.options.keepNames && nameToKeep != "" {
		name := nameFunc()
		keepNameStmt = p.keepStmtSymbolName(name.Loc, name.Data.(*ast.EIdentifier).Ref, nameToKeep)
	}

	// Pack the class back into a statement, with potentially some extra
	// statements afterwards
	var stmts []ast.Stmt
	var nameForClassDecorators ast.LocRef
	generatedLocalStmt := false
	if len(class.TSDecorators) > 0 || hasPotentialShadowCaptureEscape || classLoweringInfo.avoidTDZ {
		generatedLocalStmt = true
		name := nameFunc()
		nameRef := name.Data.(*ast.EIdentifier).Ref
		nameForClassDecorators = ast.LocRef{Loc: name.Loc, Ref: nameRef}
		classExpr := ast.EClass{Class: *class}
		class = &classExpr.Class
		init := ast.Expr{Loc: classLoc, Data: &classExpr}

		if hasPotentialShadowCaptureEscape && len(class.TSDecorators) == 0 {
			// If something captures the shadowing name and escapes the class body,
			// make a new constant to store the class and forward that value to a
			// mutable alias. That way if the alias is mutated, everything bound to
			// the original constant doesn't change.
			//
			//   class Foo {
			//     static foo() { return this.#foo() }
			//     static #foo() { return Foo }
			//   }
			//   Foo = class Bar {}
			//
			// becomes:
			//
			//   var _foo, foo_fn;
			//   const Foo2 = class {
			//     static foo() {
			//       return __privateMethod(this, _foo, foo_fn).call(this);
			//     }
			//   };
			//   let Foo = Foo2;
			//   _foo = new WeakSet();
			//   foo_fn = function() {
			//     return Foo2;
			//   };
			//   _foo.add(Foo);
			//   Foo = class Bar {
			//   };
			//
			// Generate a new symbol instead of using the shadowing name directly
			// because the shadowing name isn't a top-level symbol and we are now
			// making a top-level symbol. This symbol must be minified along with
			// other top-level symbols to avoid name collisions.
			captureRef := p.newSymbol(ast.SymbolOther, p.symbols[shadowRef.InnerIndex].OriginalName)
			p.currentScope.Generated = append(p.currentScope.Generated, captureRef)
			p.recordDeclaredSymbol(captureRef)
			p.mergeSymbols(shadowRef, captureRef)
			stmts = append(stmts, ast.Stmt{Loc: classLoc, Data: &ast.SLocal{
				Kind: p.selectLocalKind(ast.LocalConst),
				Decls: []ast.Decl{{
					Binding:    ast.Binding{Loc: name.Loc, Data: &ast.BIdentifier{Ref: captureRef}},
					ValueOrNil: init,
				}},
			}})
			init = ast.Expr{Loc: classLoc, Data: &ast.EIdentifier{Ref: captureRef}}
			p.recordUsage(captureRef)
		} else {
			// If there are class decorators, then we actually need to mutate the
			// immutable "const" binding that shadows everything in the class body.
			// The official TypeScript compiler does this by rewriting all class name
			// references in the class body to another temporary variable. This is
			// basically what we're doing here.
			if shadowRef != ast.InvalidRef {
				p.mergeSymbols(shadowRef, nameRef)
			}
		}

		// Generate the variable statement that will represent the class statement
		stmts = append(stmts, ast.Stmt{Loc: classLoc, Data: &ast.SLocal{
			Kind:     p.selectLocalKind(ast.LocalLet),
			IsExport: kind == classKindExportStmt,
			Decls: []ast.Decl{{
				Binding:    ast.Binding{Loc: name.Loc, Data: &ast.BIdentifier{Ref: nameRef}},
				ValueOrNil: init,
			}},
		}})
	} else {
		switch kind {
		case classKindStmt:
			stmts = append(stmts, ast.Stmt{Loc: classLoc, Data: &ast.SClass{Class: *class}})
		case classKindExportStmt:
			stmts = append(stmts, ast.Stmt{Loc: classLoc, Data: &ast.SClass{Class: *class, IsExport: true}})
		case classKindExportDefaultStmt:
			stmts = append(stmts, ast.Stmt{Loc: classLoc, Data: &ast.SExportDefault{
				DefaultName: defaultName,
				Value:       ast.Stmt{Loc: classLoc, Data: &ast.SClass{Class: *class}},
			}})
		}

		// The shadowing name inside the class statement should be the same as
		// the class statement name itself
		if class.Name != nil && shadowRef != ast.InvalidRef {
			p.mergeSymbols(shadowRef, class.Name.Ref)
		}
	}
	if keepNameStmt.Data != nil {
		stmts = append(stmts, keepNameStmt)
	}

	// The official TypeScript compiler adds generated code after the class body
	// in this exact order. Matching this order is important for correctness.
	if computedPropertyCache.Data != nil {
		stmts = append(stmts, ast.Stmt{Loc: expr.Loc, Data: &ast.SExpr{Value: computedPropertyCache}})
	}
	for _, expr := range privateMembers {
		stmts = append(stmts, ast.Stmt{Loc: expr.Loc, Data: &ast.SExpr{Value: expr}})
	}
	for _, expr := range staticPrivateMethods {
		stmts = append(stmts, ast.Stmt{Loc: expr.Loc, Data: &ast.SExpr{Value: expr}})
	}
	for _, expr := range staticMembers {
		stmts = append(stmts, ast.Stmt{Loc: expr.Loc, Data: &ast.SExpr{Value: expr}})
	}
	for _, expr := range instanceDecorators {
		stmts = append(stmts, ast.Stmt{Loc: expr.Loc, Data: &ast.SExpr{Value: expr}})
	}
	for _, expr := range staticDecorators {
		stmts = append(stmts, ast.Stmt{Loc: expr.Loc, Data: &ast.SExpr{Value: expr}})
	}
	if len(class.TSDecorators) > 0 {
		stmts = append(stmts, ast.AssignStmt(
			ast.Expr{Loc: nameForClassDecorators.Loc, Data: &ast.EIdentifier{Ref: nameForClassDecorators.Ref}},
			p.callRuntime(classLoc, "__decorateClass", []ast.Expr{
				{Loc: classLoc, Data: &ast.EArray{Items: class.TSDecorators}},
				{Loc: nameForClassDecorators.Loc, Data: &ast.EIdentifier{Ref: nameForClassDecorators.Ref}},
			}),
		))
		p.recordUsage(nameForClassDecorators.Ref)
		p.recordUsage(nameForClassDecorators.Ref)
	}
	if generatedLocalStmt {
		// "export default class x {}" => "class x {} export {x as default}"
		if kind == classKindExportDefaultStmt {
			stmts = append(stmts, ast.Stmt{Loc: classLoc, Data: &ast.SExportClause{
				Items: []ast.ClauseItem{{Alias: "default", Name: defaultName}},
			}})
		}

		// Calling "nameFunc" will set the class name, but we don't want it to have
		// one. If the class name was necessary, we would have already split it off
		// into a variable above. Reset it back to empty here now that we know we
		// won't call "nameFunc" after this point.
		class.Name = nil
	}
	return stmts, ast.Expr{}
}

func (p *parser) lowerTemplateLiteral(loc logger.Loc, e *ast.ETemplate) ast.Expr {
	// If there is no tag, turn this into normal string concatenation
	if e.TagOrNil.Data == nil {
		var value ast.Expr

		// Handle the head
		value = ast.Expr{Loc: loc, Data: &ast.EString{
			Value:          e.HeadCooked,
			LegacyOctalLoc: e.LegacyOctalLoc,
		}}

		// Handle the tail. Each one is handled with a separate call to ".concat()"
		// to handle various corner cases in the specification including:
		//
		//   * For objects, "toString" must be called instead of "valueOf"
		//   * Side effects must happen inline instead of at the end
		//   * Passing a "Symbol" instance should throw
		//
		for _, part := range e.Parts {
			var args []ast.Expr
			if len(part.TailCooked) > 0 {
				args = []ast.Expr{part.Value, {Loc: part.TailLoc, Data: &ast.EString{Value: part.TailCooked}}}
			} else {
				args = []ast.Expr{part.Value}
			}
			value = ast.Expr{Loc: loc, Data: &ast.ECall{
				Target: ast.Expr{Loc: loc, Data: &ast.EDot{
					Target:  value,
					Name:    "concat",
					NameLoc: part.Value.Loc,
				}},
				Args: args,
			}}
		}

		return value
	}

	// Otherwise, call the tag with the template object
	needsRaw := false
	cooked := []ast.Expr{}
	raw := []ast.Expr{}
	args := make([]ast.Expr, 0, 1+len(e.Parts))
	args = append(args, ast.Expr{})

	// Handle the head
	if e.HeadCooked == nil {
		cooked = append(cooked, ast.Expr{Loc: e.HeadLoc, Data: ast.EUndefinedShared})
		needsRaw = true
	} else {
		cooked = append(cooked, ast.Expr{Loc: e.HeadLoc, Data: &ast.EString{Value: e.HeadCooked}})
		if !lexer.UTF16EqualsString(e.HeadCooked, e.HeadRaw) {
			needsRaw = true
		}
	}
	raw = append(raw, ast.Expr{Loc: e.HeadLoc, Data: &ast.EString{Value: lexer.StringToUTF16(e.HeadRaw)}})

	// Handle the tail
	for _, part := range e.Parts {
		args = append(args, part.Value)
		if part.TailCooked == nil {
			cooked = append(cooked, ast.Expr{Loc: part.TailLoc, Data: ast.EUndefinedShared})
			needsRaw = true
		} else {
			cooked = append(cooked, ast.Expr{Loc: part.TailLoc, Data: &ast.EString{Value: part.TailCooked}})
			if !lexer.UTF16EqualsString(part.TailCooked, part.TailRaw) {
				needsRaw = true
			}
		}
		raw = append(raw, ast.Expr{Loc: part.TailLoc, Data: &ast.EString{Value: lexer.StringToUTF16(part.TailRaw)}})
	}

	// Construct the template object
	cookedArray := ast.Expr{Loc: e.HeadLoc, Data: &ast.EArray{Items: cooked, IsSingleLine: true}}
	var arrays []ast.Expr
	if needsRaw {
		arrays = []ast.Expr{cookedArray, {Loc: e.HeadLoc, Data: &ast.EArray{Items: raw, IsSingleLine: true}}}
	} else {
		arrays = []ast.Expr{cookedArray}
	}
	templateObj := p.callRuntime(e.HeadLoc, "__template", arrays)

	// Cache it in a temporary object (required by the specification)
	tempRef := p.generateTopLevelTempRef()
	args[0] = ast.Expr{Loc: loc, Data: &ast.EBinary{
		Op:   ast.BinOpLogicalOr,
		Left: ast.Expr{Loc: loc, Data: &ast.EIdentifier{Ref: tempRef}},
		Right: ast.Expr{Loc: loc, Data: &ast.EBinary{
			Op:    ast.BinOpAssign,
			Left:  ast.Expr{Loc: loc, Data: &ast.EIdentifier{Ref: tempRef}},
			Right: templateObj,
		}},
	}}

	// Call the tag function
	return ast.Expr{Loc: loc, Data: &ast.ECall{
		Target: e.TagOrNil,
		Args:   args,
	}}
}

func (p *parser) shouldLowerSuperPropertyAccess(expr ast.Expr) bool {
	if p.fnOrArrowDataVisit.shouldLowerSuper {
		_, isSuper := expr.Data.(*ast.ESuper)
		return isSuper
	}
	return false
}

func (p *parser) ensureSuperGet() {
	ref := &p.fnOnlyDataVisit.superHelpers.getRef
	if *ref == ast.InvalidRef {
		*ref = p.newSymbol(ast.SymbolOther, "__superGet")
	}
	p.recordUsage(*ref)
}

func (p *parser) ensureSuperSet() {
	ref := &p.fnOnlyDataVisit.superHelpers.setRef
	if *ref == ast.InvalidRef {
		*ref = p.newSymbol(ast.SymbolOther, "__superSet")
	}
	p.recordUsage(*ref)
}

func (p *parser) callSuperPropertyWrapper(loc logger.Loc, property ast.Expr, includeGet bool) ast.Expr {
	var result ast.Expr

	if thisRef := p.fnOnlyDataVisit.thisClassStaticRef; thisRef != nil {
		p.recordUsage(*thisRef)
		result = p.callRuntime(loc, "__superStaticWrapper", []ast.Expr{
			{Loc: loc, Data: &ast.EIdentifier{Ref: *thisRef}},
			property,
		})
	} else {
		// Only some uses of the wrapper need to read
		superGet := ast.Expr{Loc: loc, Data: ast.ENullShared}
		if includeGet {
			p.ensureSuperGet()
			superGet.Data = &ast.EIdentifier{Ref: p.fnOnlyDataVisit.superHelpers.getRef}
		}

		// All uses of the wrapper need to write
		p.ensureSuperSet()
		superSet := ast.Expr{Loc: loc, Data: &ast.EIdentifier{Ref: p.fnOnlyDataVisit.superHelpers.setRef}}

		result = p.callRuntime(loc, "__superWrapper", []ast.Expr{
			superGet,
			superSet,
			property,
		})
	}

	return ast.Expr{Loc: loc, Data: &ast.EDot{Target: result, Name: "_", NameLoc: loc}}
}

func (p *parser) lowerSuperPropertyGet(loc logger.Loc, key ast.Expr) ast.Expr {
	if thisRef := p.fnOnlyDataVisit.thisClassStaticRef; thisRef != nil {
		p.recordUsage(*thisRef)
		return p.callRuntime(loc, "__superStaticGet", []ast.Expr{
			{Loc: loc, Data: &ast.EIdentifier{Ref: *thisRef}},
			key,
		})
	}

	// "super.foo" => "__superGet('foo')"
	// "super[foo]" => "__superGet(foo)"
	p.ensureSuperGet()
	return ast.Expr{Loc: loc, Data: &ast.ECall{
		Target: ast.Expr{Loc: loc, Data: &ast.EIdentifier{Ref: p.fnOnlyDataVisit.superHelpers.getRef}},
		Args:   []ast.Expr{key},
	}}
}

func (p *parser) lowerSuperPropertySet(loc logger.Loc, key ast.Expr, value ast.Expr) ast.Expr {
	if thisRef := p.fnOnlyDataVisit.thisClassStaticRef; thisRef != nil {
		p.recordUsage(*thisRef)
		return p.callRuntime(loc, "__superStaticSet", []ast.Expr{
			{Loc: loc, Data: &ast.EIdentifier{Ref: *thisRef}},
			key,
			value,
		})
	}

	// "super.foo = bar" => "__superSet('foo', bar)"
	// "super[foo] = bar" => "__superSet(foo, bar)"
	p.ensureSuperSet()
	return ast.Expr{Loc: loc, Data: &ast.ECall{
		Target: ast.Expr{Loc: loc, Data: &ast.EIdentifier{Ref: p.fnOnlyDataVisit.superHelpers.setRef}},
		Args:   []ast.Expr{key, value},
	}}
}

func (p *parser) lowerSuperPropertySetBinOp(loc logger.Loc, property ast.Expr, op ast.OpCode, value ast.Expr) ast.Expr {
	// "super.foo += bar" => "__superSet('foo', __superGet('foo') + bar)"
	// "super[foo] += bar" => "__superSet(foo, __superGet(foo) + bar)"
	// "super[foo()] += bar" => "__superSet(_a = foo(), __superGet(_a) + bar)"
	targetFunc, targetWrapFunc := p.captureValueWithPossibleSideEffects(property.Loc, 2, property, valueDefinitelyNotMutated)
	return targetWrapFunc(p.lowerSuperPropertySet(loc, targetFunc(), ast.Expr{Loc: value.Loc, Data: &ast.EBinary{
		Op:    op,
		Left:  p.lowerSuperPropertyGet(loc, targetFunc()),
		Right: value,
	}}))
}

func (p *parser) maybeLowerSuperPropertyGetInsideCall(call *ast.ECall) {
	var key ast.Expr

	switch e := call.Target.Data.(type) {
	case *ast.EDot:
		// Lower "super.prop" if necessary
		if !p.shouldLowerSuperPropertyAccess(e.Target) {
			return
		}
		key = ast.Expr{Loc: e.NameLoc, Data: &ast.EString{Value: lexer.StringToUTF16(e.Name)}}

	case *ast.EIndex:
		// Lower "super[prop]" if necessary
		if !p.shouldLowerSuperPropertyAccess(e.Target) {
			return
		}
		key = e.Index

	default:
		return
	}

	// "super.foo(a, b)" => "__superIndex('foo').call(this, a, b)"
	call.Target.Data = &ast.EDot{
		Target:  p.lowerSuperPropertyGet(call.Target.Loc, key),
		NameLoc: key.Loc,
		Name:    "call",
	}
	thisExpr := ast.Expr{Loc: call.Target.Loc, Data: ast.EThisShared}
	call.Args = append([]ast.Expr{thisExpr}, call.Args...)
}

func couldPotentiallyThrow(data ast.E) bool {
	switch data.(type) {
	case *ast.ENull, *ast.EUndefined, *ast.EBoolean, *ast.ENumber,
		*ast.EBigInt, *ast.EString, *ast.EFunction, *ast.EArrow:
		return false
	}
	return true
}

func (p *parser) maybeLowerSetBinOp(left ast.Expr, op ast.OpCode, right ast.Expr) ast.Expr {
	if target, loc, private := p.extractPrivateIndex(left); private != nil {
		return p.lowerPrivateSetBinOp(target, loc, private, op, right)
	}
	if property := p.extractSuperProperty(left); property.Data != nil {
		return p.lowerSuperPropertySetBinOp(left.Loc, property, op, right)
	}
	return ast.Expr{}
}