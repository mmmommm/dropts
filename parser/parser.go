package parser

import (
	// "encoding/base64"
	"fmt"
	"io/fs"
	// "sort"

	// "github.com/mmmommm/dropts/lexer"
	"github.com/mmmommm/dropts/graph"
	"github.com/mmmommm/dropts/helpers"
	"github.com/mmmommm/dropts/ast"
	"github.com/mmmommm/dropts/logger"
	"github.com/mmmommm/dropts/config"
)

type scannerFile struct {
	inputFile  graph.InputFile
	pluginData interface{}

	// If "AbsMetadataFile" is present, this will be filled out with information
	// about this file in JSON format. This is a partial JSON file that will be
	// fully assembled later.
	jsonMetadataChunk string
}

type tlaCheck struct {
	parent            ast.Index32
	depth             uint32
	importRecordIndex uint32
}

type parseArgs struct {
	fs              fs.FS
	log             logger.Log
	// res             resolver.Resolver
	// caches          *cache.CacheSet
	keyPath         logger.Path
	prettyPath      string
	sourceIndex     uint32
	importSource    *logger.Source
	// sideEffects     graph.SideEffects
	// importPathRange logger.Range
	pluginData      interface{}
	options         config.Options
	results         chan parseResult
	// inject          chan config.InjectedFile
	skipResolve     bool
	uniqueKeyPrefix string
}

type parseResult struct {
	file           scannerFile
	// resolveResults []*resolver.ResolveResult
	tlaCheck       tlaCheck
	ok             bool
}


func parseFile(args parseArgs) {
	source := logger.Source{
		Index:          args.sourceIndex,
		KeyPath:        args.keyPath,
		PrettyPath:     args.prettyPath,
		IdentifierName: ast.GenerateNonUniqueNameFromPath(args.keyPath.Text),
	}

	var loader config.Loader
	// var absResolveDir string
	// var pluginName string
	var pluginData interface{}

	if stdin := args.options.Stdin; stdin != nil {
		// Special-case stdin
		source.Contents = stdin.Contents
		loader = stdin.Loader
		if loader == config.LoaderNone {
			loader = config.LoaderJS
		}
		// absResolveDir = args.options.Stdin.AbsResolveDir
	} else {
		// result, ok := runOnLoadPlugins(
		// 	args.options.Plugins,
		// 	// args.res,
		// 	args.fs,
		// 	// &args.caches.FSCache,
		// 	args.log,
		// 	&source,
		// 	args.importSource,
		// 	// args.importPathRange,
		// 	args.pluginData,
		// 	args.options.WatchMode,
		// )
		// if !ok {
		// 	// if args.inject != nil {
		// 	// 	args.inject <- config.InjectedFile{
		// 	// 		Source: source,
		// 	// 	}
		// 	// }
		// 	args.results <- parseResult{}
		// 	return
		// }
		// loader = result.loader
		// // absResolveDir = result.absResolveDir
		// // pluginName = result.pluginName
		// pluginData = result.pluginData
	}

	// _, base, ext := logger.PlatformIndependentPathDirBaseExt(source.KeyPath.Text)

	// The special "default" loader determines the loader from the file path
	// if loader == config.LoaderDefault {
	// 	loader = loaderFromFileExtension(args.options.ExtensionToLoader, base+ext)
	// }

	result := parseResult{
		file: scannerFile{
			inputFile: graph.InputFile{
				Source:      source,
				Loader:      loader,
				// SideEffects: args.sideEffects,
			},
			pluginData: pluginData,
		},
	}

	defer func() {
		r := recover()
		if r != nil {
			args.log.AddWithNotes(logger.Error, nil, logger.Range{},
				fmt.Sprintf("panic: %v (while parsing %q)", r, source.PrettyPath),
				[]logger.MsgData{{Text: helpers.PrettyPrintedStack()}})
			args.results <- result
		}
	}()

	// tsだけ対応する予定なので一旦コメントアウト

	// switch loader {
	// case config.LoaderJS:
	// 	ast, ok := args.caches.JSCache.Parse(args.log, source, OptionsFromConfig(&args.options))
	// 	if len(ast.Parts) <= 1 { // Ignore the implicitly-generated namespace export part
	// 		result.file.inputFile.SideEffects.Kind = graph.NoSideEffects_EmptyAST
	// 	}
	// 	result.file.inputFile.Repr = &graph.JSRepr{AST: ast}
	// 	result.ok = ok

	// case config.LoaderJSX:
	// 	args.options.JSX.Parse = true
	// 	ast, ok := args.caches.JSCache.Parse(args.log, source, OptionsFromConfig(&args.options))
	// 	if len(ast.Parts) <= 1 { // Ignore the implicitly-generated namespace export part
	// 		result.file.inputFile.SideEffects.Kind = graph.NoSideEffects_EmptyAST
	// 	}
	// 	result.file.inputFile.Repr = &graph.JSRepr{AST: ast}
	// 	result.ok = ok

	// case config.LoaderTS, config.LoaderTSNoAmbiguousLessThan:
	// 	args.options.TS.Parse = true
	// 	args.options.TS.NoAmbiguousLessThan = loader == config.LoaderTSNoAmbiguousLessThan
	// 	ast, ok := args.caches.JSCache.Parse(args.log, source, OptionsFromConfig(&args.options))
	// 	if len(ast.Parts) <= 1 { // Ignore the implicitly-generated namespace export part
	// 		result.file.inputFile.SideEffects.Kind = graph.NoSideEffects_EmptyAST
	// 	}
	// 	result.file.inputFile.Repr = &graph.JSRepr{AST: ast}
	// 	result.ok = ok

	// case config.LoaderTSX:
	// 	args.options.TS.Parse = true
	// 	args.options.JSX.Parse = true
	// 	ast, ok := args.caches.JSCache.Parse(args.log, source, OptionsFromConfig(&args.options))
	// 	if len(ast.Parts) <= 1 { // Ignore the implicitly-generated namespace export part
	// 		result.file.inputFile.SideEffects.Kind = graph.NoSideEffects_EmptyAST
	// 	}
	// 	result.file.inputFile.Repr = &graph.JSRepr{AST: ast}
	// 	result.ok = ok

	// case config.LoaderCSS:
	// 	ast := args.caches.CSSCache.Parse(args.log, source, css_parser.Options{
	// 		MangleSyntax:           args.options.MangleSyntax,
	// 		RemoveWhitespace:       args.options.RemoveWhitespace,
	// 		UnsupportedCSSFeatures: args.options.UnsupportedCSSFeatures,
	// 	})
	// 	result.file.inputFile.Repr = &graph.CSSRepr{AST: ast}
	// 	result.ok = true

	// case config.LoaderJSON:
	// 	expr, ok := args.caches.JSONCache.Parse(args.log, source, JSONOptions{})
	// 	ast := LazyExportAST(args.log, source, OptionsFromConfig(&args.options), expr, "")
	// 	if pluginName != "" {
	// 		result.file.inputFile.SideEffects.Kind = graph.NoSideEffects_PureData_FromPlugin
	// 	} else {
	// 		result.file.inputFile.SideEffects.Kind = graph.NoSideEffects_PureData
	// 	}
	// 	result.file.inputFile.Repr = &graph.JSRepr{AST: ast}
	// 	result.ok = ok

	// case config.LoaderText:
	// 	encoded := base64.StdEncoding.EncodeToString([]byte(source.Contents))
	// 	expr := ast.Expr{Data: &ast.EString{Value: lexer.StringToUTF16(source.Contents)}}
	// 	ast := LazyExportAST(args.log, source, OptionsFromConfig(&args.options), expr, "")
	// 	ast.URLForCSS = "data:text/plain;base64," + encoded
	// 	if pluginName != "" {
	// 		result.file.inputFile.SideEffects.Kind = graph.NoSideEffects_PureData_FromPlugin
	// 	} else {
	// 		result.file.inputFile.SideEffects.Kind = graph.NoSideEffects_PureData
	// 	}
	// 	result.file.inputFile.Repr = &graph.JSRepr{AST: ast}
	// 	result.ok = true

	// case config.LoaderBase64:
	// 	mimeType := guessMimeType(ext, source.Contents)
	// 	encoded := base64.StdEncoding.EncodeToString([]byte(source.Contents))
	// 	expr := ast.Expr{Data: &ast.EString{Value: lexer.StringToUTF16(encoded)}}
	// 	ast := LazyExportAST(args.log, source, OptionsFromConfig(&args.options), expr, "")
	// 	ast.URLForCSS = "data:" + mimeType + ";base64," + encoded
	// 	if pluginName != "" {
	// 		result.file.inputFile.SideEffects.Kind = graph.NoSideEffects_PureData_FromPlugin
	// 	} else {
	// 		result.file.inputFile.SideEffects.Kind = graph.NoSideEffects_PureData
	// 	}
	// 	result.file.inputFile.Repr = &graph.JSRepr{AST: ast}
	// 	result.ok = true

	// case config.LoaderBinary:
	// 	encoded := base64.StdEncoding.EncodeToString([]byte(source.Contents))
	// 	expr := ast.Expr{Data: &ast.EString{Value: lexer.StringToUTF16(encoded)}}
	// 	helper := "__toBinary"
	// 	if args.options.Platform == config.PlatformNode {
	// 		helper = "__toBinaryNode"
	// 	}
	// 	ast := LazyExportAST(args.log, source, OptionsFromConfig(&args.options), expr, helper)
	// 	ast.URLForCSS = "data:application/octet-stream;base64," + encoded
	// 	if pluginName != "" {
	// 		result.file.inputFile.SideEffects.Kind = graph.NoSideEffects_PureData_FromPlugin
	// 	} else {
	// 		result.file.inputFile.SideEffects.Kind = graph.NoSideEffects_PureData
	// 	}
	// 	result.file.inputFile.Repr = &graph.JSRepr{AST: ast}
	// 	result.ok = true

	// case config.LoaderDataURL:
	// 	mimeType := guessMimeType(ext, source.Contents)
	// 	encoded := base64.StdEncoding.EncodeToString([]byte(source.Contents))
	// 	url := fmt.Sprintf("data:%s;base64,%s", mimeType, encoded)
	// 	expr := ast.Expr{Data: &ast.EString{Value: lexer.StringToUTF16(url)}}
	// 	ast := LazyExportAST(args.log, source, OptionsFromConfig(&args.options), expr, "")
	// 	ast.URLForCSS = url
	// 	if pluginName != "" {
	// 		result.file.inputFile.SideEffects.Kind = graph.NoSideEffects_PureData_FromPlugin
	// 	} else {
	// 		result.file.inputFile.SideEffects.Kind = graph.NoSideEffects_PureData
	// 	}
	// 	result.file.inputFile.Repr = &graph.JSRepr{AST: ast}
	// 	result.ok = true

	// case config.LoaderFile:
	// 	uniqueKey := fmt.Sprintf("%sA%08d", args.uniqueKeyPrefix, args.sourceIndex)
	// 	uniqueKeyPath := uniqueKey + source.KeyPath.IgnoredSuffix
	// 	expr := ast.Expr{Data: &ast.EString{Value: lexer.StringToUTF16(uniqueKeyPath)}}
	// 	ast := LazyExportAST(args.log, source, OptionsFromConfig(&args.options), expr, "")
	// 	ast.URLForCSS = uniqueKeyPath
	// 	if pluginName != "" {
	// 		result.file.inputFile.SideEffects.Kind = graph.NoSideEffects_PureData_FromPlugin
	// 	} else {
	// 		result.file.inputFile.SideEffects.Kind = graph.NoSideEffects_PureData
	// 	}
	// 	result.file.inputFile.Repr = &graph.JSRepr{AST: ast}
	// 	result.ok = true

	// 	// Mark that this file is from the "file" loader
	// 	result.file.inputFile.UniqueKeyForFileLoader = uniqueKey

	// default:
	// 	var message string
	// 	if source.KeyPath.Namespace == "file" && ext != "" {
	// 		message = fmt.Sprintf("No loader is configured for %q files: %s", ext, source.PrettyPath)
	// 	} else {
	// 		message = fmt.Sprintf("Do not know how to load path: %s", source.PrettyPath)
	// 	}
	// 	tracker := logger.MakeLineColumnTracker(args.importSource)
	// 	args.log.Add(logger.Error, &tracker, args.importPathRange, message)
	// }

	// This must come before we send on the "results" channel to avoid deadlock
	// if args.inject != nil {
	// 	var exports []config.InjectableExport
	// 	if repr, ok := result.file.inputFile.Repr.(*graph.JSRepr); ok {
	// 		aliases := make([]string, 0, len(repr.AST.NamedExports))
	// 		for alias := range repr.AST.NamedExports {
	// 			aliases = append(aliases, alias)
	// 		}
	// 		sort.Strings(aliases) // Sort for determinism
	// 		exports = make([]config.InjectableExport, len(aliases))
	// 		for i, alias := range aliases {
	// 			exports[i] = config.InjectableExport{
	// 				Alias: alias,
	// 				Loc:   repr.AST.NamedExports[alias].AliasLoc,
	// 			}
	// 		}
	// 	}
	// 	args.inject <- config.InjectedFile{
	// 		Source:  source,
	// 		Exports: exports,
	// 	}
	// }

	// Stop now if parsing failed
	if !result.ok {
		args.results <- result
		return
	}

	// Run the resolver on the parse thread so it's not run on the main thread.
	// That way the main thread isn't blocked if the resolver takes a while.
	if args.options.Mode == config.ModeBundle && !args.skipResolve {
		// Clone the import records because they will be mutated later
		recordsPtr := result.file.inputFile.Repr.ImportRecords()
		records := append([]ast.ImportRecord{}, *recordsPtr...)
		*recordsPtr = records
		// result.resolveResults = make([]*resolver.ResolveResult, len(records))

		if len(records) > 0 {
			// resolverCache := make(map[ast.ImportKind]map[string]*resolver.ResolveResult)
			// tracker := logger.MakeLineColumnTracker(&source)

			for importRecordIndex := range records {
				// Don't try to resolve imports that are already resolved
				record := &records[importRecordIndex]
				if record.SourceIndex.IsValid() {
					continue
				}

				// Ignore records that the parser has discarded. This is used to remove
				// type-only imports in TypeScript files.
				if record.IsUnused {
					continue
				}

				// Cache the path in case it's imported multiple times in this file
				// cache, ok := resolverCache[record.Kind]
				// if !ok {
				// 	cache = make(map[string]*resolver.ResolveResult)
				// 	resolverCache[record.Kind] = cache
				// }
				// if resolveResult, ok := cache[record.Path.Text]; ok {
				// 	result.resolveResults[importRecordIndex] = resolveResult
				// 	continue
				// }

				// Run the resolver and log an error if the path couldn't be resolved
				// resolveResult, didLogError, debug := runOnResolvePlugins(
				// 	args.options.Plugins,
				// 	args.res,
				// 	args.log,
				// 	args.fs,
				// 	&args.caches.FSCache,
				// 	&source,
				// 	record.Range,
				// 	source.KeyPath.Namespace,
				// 	record.Path.Text,
				// 	record.Kind,
				// 	absResolveDir,
				// 	pluginData,
				// )
				// cache[record.Path.Text] = resolveResult

				// All "require.resolve()" imports should be external because we don't
				// want to waste effort traversing into them
				// if record.Kind == ast.ImportRequireResolve {
				// 	if resolveResult != nil && resolveResult.IsExternal {
				// 		// Allow path substitution as long as the result is external
				// 		result.resolveResults[importRecordIndex] = resolveResult
				// 	} else if !record.HandlesImportErrors {
				// 		args.log.Add(logger.Warning, &tracker, record.Range,
				// 			fmt.Sprintf("%q should be marked as external for use with \"require.resolve\"", record.Path.Text))
				// 	}
				// 	continue
				// }

				// if resolveResult == nil {
				// 	// Failed imports inside a try/catch are silently turned into
				// 	// external imports instead of causing errors. This matches a common
				// 	// code pattern for conditionally importing a module with a graceful
				// 	// fallback.
				// 	if !didLogError && !record.HandlesImportErrors {
				// 		hint := ""
				// 		if resolver.IsPackagePath(record.Path.Text) {
				// 			hint = fmt.Sprintf("You can mark the path %q as external to exclude it from the bundle, which will remove this error.", record.Path.Text)
				// 			if record.Kind == ast.ImportRequire {
				// 				hint += " You can also surround this \"require\" call with a try/catch block to handle this failure at run-time instead of bundle-time."
				// 			} else if record.Kind == ast.ImportDynamic {
				// 				hint += " You can also add \".catch()\" here to handle this failure at run-time instead of bundle-time."
				// 			}
				// 			if pluginName == "" && !args.fs.IsAbs(record.Path.Text) {
				// 				if query := args.res.ProbeResolvePackageAsRelative(absResolveDir, record.Path.Text, record.Kind); query != nil {
				// 					hint = fmt.Sprintf("Use the relative path %q to reference the file %q. "+
				// 						"Without the leading \"./\", the path %q is being interpreted as a package path instead.",
				// 						"./"+record.Path.Text, args.res.PrettyPath(query.PathPair.Primary), record.Path.Text)
				// 				}
				// 			}
				// 		}
				// 		if args.options.Platform != config.PlatformNode {
				// 			if _, ok := resolver.BuiltInNodeModules[record.Path.Text]; ok {
				// 				var how string
				// 				switch logger.API {
				// 				case logger.CLIAPI:
				// 					how = "--platform=node"
				// 				case logger.JSAPI:
				// 					how = "platform: 'node'"
				// 				case logger.GoAPI:
				// 					how = "Platform: api.PlatformNode"
				// 				}
				// 				hint = fmt.Sprintf("The package %q wasn't found on the file system but is built into node. "+
				// 					"Are you trying to bundle for node? You can use %q to do that, which will remove this error.", record.Path.Text, how)
				// 			}
				// 		}
				// 		if absResolveDir == "" && pluginName != "" {
				// 			hint = fmt.Sprintf("The plugin %q didn't set a resolve directory for the file %q, "+
				// 				"so esbuild did not search for %q on the file system.", pluginName, source.PrettyPath, record.Path.Text)
				// 		}
				// 		var notes []logger.MsgData
				// 		if hint != "" {
				// 			notes = append(notes, logger.MsgData{Text: hint})
				// 		}
				// 		debug.LogErrorMsg(args.log, &source, record.Range, fmt.Sprintf("Could not resolve %q", record.Path.Text), notes)
				// 	} else if args.log.Level <= logger.LevelDebug && !didLogError && record.HandlesImportErrors {
				// 		args.log.Add(logger.Debug, &tracker, record.Range,
				// 			fmt.Sprintf("Importing %q was allowed even though it could not be resolved because dynamic import failures appear to be handled here:",
				// 				record.Path.Text))
				// 	}
				// 	continue
				// }

				// result.resolveResults[importRecordIndex] = resolveResult
			}
		}
	}

	// Attempt to parse the source map if present
	// if loader.CanHaveSourceMap() && args.options.SourceMap != config.SourceMapNone {
	// 	var sourceMapComment logger.Span
	// 	switch repr := result.file.inputFile.Repr.(type) {
	// 	case *graph.JSRepr:
	// 		sourceMapComment = repr.AST.SourceMapComment
		// case *graph.CSSRepr:
		// 	sourceMapComment = repr.AST.SourceMapComment
		//}
		// if sourceMapComment.Text != "" {
		// 	if path, contents := extractSourceMapFromComment(args.log, args.fs, &args.caches.FSCache,
		// 		args.res, &source, sourceMapComment, absResolveDir); contents != nil {
		// 		result.file.inputFile.InputSourceMap = ParseSourceMap(args.log, logger.Source{
		// 			KeyPath:    path,
		// 			PrettyPath: args.res.PrettyPath(path),
		// 			Contents:   *contents,
		// 		})
		// 	}
		// }
	//}

	args.results <- result
}
