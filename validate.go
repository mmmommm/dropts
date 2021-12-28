package main

import (
	"fmt"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"io/fs"

	// "github.com/mmmommm/dropts/api_helpers"
	"github.com/mmmommm/dropts/compat"
	"github.com/mmmommm/dropts/config"
	"github.com/mmmommm/dropts/lexer"
	"github.com/mmmommm/dropts/parser"
	"github.com/mmmommm/dropts/logger"
)

func validatePathTemplate(template string) []config.PathTemplate {
	if template == "" {
		return nil
	}
	template = "./" + strings.ReplaceAll(template, "\\", "/")

	parts := make([]config.PathTemplate, 0, 4)
	search := 0

	// Split by placeholders
	for search < len(template) {
		// Jump to the next "["
		if found := strings.IndexByte(template[search:], '['); found == -1 {
			break
		} else {
			search += found
		}
		head, tail := template[:search], template[search:]
		placeholder := config.NoPlaceholder

		// Check for a placeholder
		switch {
		case strings.HasPrefix(tail, "[dir]"):
			placeholder = config.DirPlaceholder
			search += len("[dir]")

		case strings.HasPrefix(tail, "[name]"):
			placeholder = config.NamePlaceholder
			search += len("[name]")

		case strings.HasPrefix(tail, "[hash]"):
			placeholder = config.HashPlaceholder
			search += len("[hash]")

		case strings.HasPrefix(tail, "[ext]"):
			placeholder = config.ExtPlaceholder
			search += len("[ext]")

		default:
			// Skip past the "[" so we don't find it again
			search++
			continue
		}

		// Add a part for everything up to and including this placeholder
		parts = append(parts, config.PathTemplate{
			Data:        head,
			Placeholder: placeholder,
		})

		// Reset the search after this placeholder
		template = template[search:]
		search = 0
	}

	// Append any remaining data as a part without a placeholder
	if search < len(template) {
		parts = append(parts, config.PathTemplate{
			Data:        template,
			Placeholder: config.NoPlaceholder,
		})
	}

	return parts
}

func validatePlatform(value Platform) config.Platform {
	switch value {
	case PlatformBrowser:
		return config.PlatformBrowser
	case PlatformNode:
		return config.PlatformNode
	case PlatformNeutral:
		return config.PlatformNeutral
	default:
		panic("Invalid platform")
	}
}

func validateFormat(value Format) config.Format {
	switch value {
	case FormatDefault:
		return config.FormatPreserve
	case FormatIIFE:
		return config.FormatIIFE
	case FormatCommonJS:
		return config.FormatCommonJS
	case FormatESModule:
		return config.FormatESModule
	default:
		panic("Invalid format")
	}
}

func validateSourceMap(value SourceMap) config.SourceMap {
	switch value {
	case SourceMapNone:
		return config.SourceMapNone
	case SourceMapLinked:
		return config.SourceMapLinkedWithComment
	case SourceMapInline:
		return config.SourceMapInline
	case SourceMapExternal:
		return config.SourceMapExternalWithoutComment
	case SourceMapInlineAndExternal:
		return config.SourceMapInlineAndExternal
	default:
		panic("Invalid source map")
	}
}

func validateLegalComments(value LegalComments, bundle bool) config.LegalComments {
	switch value {
	case LegalCommentsDefault:
		if bundle {
			return config.LegalCommentsEndOfFile
		} else {
			return config.LegalCommentsInline
		}
	case LegalCommentsNone:
		return config.LegalCommentsNone
	case LegalCommentsInline:
		return config.LegalCommentsInline
	case LegalCommentsEndOfFile:
		return config.LegalCommentsEndOfFile
	case LegalCommentsLinked:
		return config.LegalCommentsLinkedWithComment
	case LegalCommentsExternal:
		return config.LegalCommentsExternalWithoutComment
	default:
		panic("Invalid source map")
	}
}

func validateColor(value StderrColor) logger.UseColor {
	switch value {
	case ColorIfTerminal:
		return logger.ColorIfTerminal
	case ColorNever:
		return logger.ColorNever
	case ColorAlways:
		return logger.ColorAlways
	default:
		panic("Invalid color")
	}
}

func validateLogLevel(value LogLevel) logger.LogLevel {
	switch value {
	case LogLevelVerbose:
		return logger.LevelVerbose
	case LogLevelDebug:
		return logger.LevelDebug
	case LogLevelInfo:
		return logger.LevelInfo
	case LogLevelWarning:
		return logger.LevelWarning
	case LogLevelError:
		return logger.LevelError
	case LogLevelSilent:
		return logger.LevelSilent
	default:
		panic("Invalid log level")
	}
}

func validateASCIIOnly(value Charset) bool {
	switch value {
	case CharsetDefault, CharsetASCII:
		return true
	case CharsetUTF8:
		return false
	default:
		panic("Invalid charset")
	}
}

func validateTreeShaking(value TreeShaking, bundle bool, format Format) bool {
	switch value {
	case TreeShakingDefault:
		// If we're in an IIFE then there's no way to concatenate additional code
		// to the end of our output so we assume tree shaking is safe. And when
		// bundling we assume that tree shaking is safe because if you want to add
		// code to the bundle, you should be doing that by including it in the
		// bundle instead of concatenating it afterward, so we also assume tree
		// shaking is safe then. Otherwise we assume tree shaking is not safe.
		return bundle || format == FormatIIFE
	case TreeShakingFalse:
		return false
	case TreeShakingTrue:
		return true
	default:
		panic("Invalid tree shaking")
	}
}

func validateLoader(value Loader) config.Loader {
	switch value {
	case LoaderNone:
		return config.LoaderNone
	case LoaderJS:
		return config.LoaderJS
	case LoaderJSX:
		return config.LoaderJSX
	case LoaderTS:
		return config.LoaderTS
	case LoaderTSX:
		return config.LoaderTSX
	case LoaderJSON:
		return config.LoaderJSON
	case LoaderText:
		return config.LoaderText
	case LoaderBase64:
		return config.LoaderBase64
	case LoaderDataURL:
		return config.LoaderDataURL
	case LoaderFile:
		return config.LoaderFile
	case LoaderBinary:
		return config.LoaderBinary
	case LoaderCSS:
		return config.LoaderCSS
	case LoaderDefault:
		return config.LoaderDefault
	default:
		panic("Invalid loader")
	}
}

func validateEngine(value EngineName) compat.Engine {
	switch value {
	case EngineChrome:
		return compat.Chrome
	case EngineEdge:
		return compat.Edge
	case EngineFirefox:
		return compat.Firefox
	case EngineIOS:
		return compat.IOS
	case EngineNode:
		return compat.Node
	case EngineSafari:
		return compat.Safari
	default:
		panic("Invalid loader")
	}
}

var versionRegex = regexp.MustCompile(`^([0-9]+)(?:\.([0-9]+))?(?:\.([0-9]+))?$`)

func validateFeatures(log logger.Log, target Target, engines []Engine) (config.TargetFromAPI, compat.JSFeature, compat.CSSFeature, string) {
	if target == DefaultTarget && len(engines) == 0 {
		return config.TargetWasUnconfigured, 0, 0, ""
	}

	constraints := make(map[compat.Engine][]int)
	targets := make([]string, 0, 1+len(engines))
	targetFromAPI := config.TargetWasConfigured

	switch target {
	case ES5:
		constraints[compat.ES] = []int{5}
	case ES2015:
		constraints[compat.ES] = []int{2015}
	case ES2016:
		constraints[compat.ES] = []int{2016}
	case ES2017:
		constraints[compat.ES] = []int{2017}
	case ES2018:
		constraints[compat.ES] = []int{2018}
	case ES2019:
		constraints[compat.ES] = []int{2019}
	case ES2020:
		constraints[compat.ES] = []int{2020}
	case ES2021:
		constraints[compat.ES] = []int{2021}
	case ESNext:
		targetFromAPI = config.TargetWasConfiguredIncludingESNext
	case DefaultTarget:
	default:
		panic("Invalid target")
	}

	for _, engine := range engines {
		if match := versionRegex.FindStringSubmatch(engine.Version); match != nil {
			if major, err := strconv.Atoi(match[1]); err == nil {
				version := []int{major}
				if minor, err := strconv.Atoi(match[2]); err == nil {
					version = append(version, minor)
				}
				if patch, err := strconv.Atoi(match[3]); err == nil {
					version = append(version, patch)
				}
				switch engine.Name {
				case EngineChrome:
					constraints[compat.Chrome] = version
				case EngineEdge:
					constraints[compat.Edge] = version
				case EngineFirefox:
					constraints[compat.Firefox] = version
				case EngineIOS:
					constraints[compat.IOS] = version
				case EngineNode:
					constraints[compat.Node] = version
				case EngineSafari:
					constraints[compat.Safari] = version
				default:
					panic("Invalid engine name")
				}
				continue
			}
		}

		log.Add(logger.Error, nil, logger.Range{}, fmt.Sprintf("Invalid version: %q", engine.Version))
	}

	for engine, version := range constraints {
		var text string
		switch len(version) {
		case 1:
			text = fmt.Sprintf("%s%d", engine.String(), version[0])
		case 2:
			text = fmt.Sprintf("%s%d.%d", engine.String(), version[0], version[1])
		case 3:
			text = fmt.Sprintf("%s%d.%d.%d", engine.String(), version[0], version[1], version[2])
		}
		targets = append(targets, fmt.Sprintf("%q", text))
	}

	sort.Strings(targets)
	targetEnv := strings.Join(targets, ", ")

	return targetFromAPI, compat.UnsupportedJSFeatures(constraints), compat.UnsupportedCSSFeatures(constraints), targetEnv
}

func validateGlobalName(log logger.Log, text string) []string {
	if text != "" {
		source := logger.Source{
			KeyPath:    logger.Path{Text: "(global path)"},
			PrettyPath: "(global name)",
			Contents:   text,
		}

		if result, ok := parser.ParseGlobalName(log, source); ok {
			return result
		}
	}

	return nil
}

func validateExternals(log logger.Log, fs fs.FS, paths []string) config.ExternalModules {
	result := config.ExternalModules{
		NodeModules: make(map[string]bool),
		AbsPaths:    make(map[string]bool),
	}
	for _, path := range paths {
		if index := strings.IndexByte(path, '*'); index != -1 {
			if strings.ContainsRune(path[index+1:], '*') {
				log.Add(logger.Error, nil, logger.Range{}, fmt.Sprintf("External path %q cannot have more than one \"*\" wildcard", path))
			} else {
				result.Patterns = append(result.Patterns, config.WildcardPattern{
					Prefix: path[:index],
					Suffix: path[index+1:],
				})
			}
		} else if resolver.IsPackagePath(path) {
			result.NodeModules[path] = true
		} else if absPath := validatePath(log, fs, path, "external path"); absPath != "" {
			result.AbsPaths[absPath] = true
		}
	}
	return result
}

func isValidExtension(ext string) bool {
	return len(ext) >= 2 && ext[0] == '.' && ext[len(ext)-1] != '.'
}

func validateResolveExtensions(log logger.Log, order []string) []string {
	if order == nil {
		return []string{".tsx", ".ts", ".jsx", ".js", ".css", ".json"}
	}
	for _, ext := range order {
		if !isValidExtension(ext) {
			log.Add(logger.Error, nil, logger.Range{}, fmt.Sprintf("Invalid file extension: %q", ext))
		}
	}
	return order
}

func validateLoaders(log logger.Log, loaders map[string]Loader) map[string]config.Loader {
	result := bundler.DefaultExtensionToLoaderMap()
	if loaders != nil {
		for ext, loader := range loaders {
			if !isValidExtension(ext) {
				log.Add(logger.Error, nil, logger.Range{}, fmt.Sprintf("Invalid file extension: %q", ext))
			}
			result[ext] = validateLoader(loader)
		}
	}
	return result
}

func validateJSXExpr(log logger.Log, text string, name string, kind parser.JSXExprKind) config.JSXExpr {
	if expr, ok := parser.ParseJSXExpr(text, kind); ok {
		return expr
	}
	log.Add(logger.Error, nil, logger.Range{}, fmt.Sprintf("Invalid JSX %s: %q", name, text))
	return config.JSXExpr{}
}

func validateDefines(
	log logger.Log,
	defines map[string]string,
	pureFns []string,
	platform Platform,
	minify bool,
) (*config.ProcessedDefines, []config.InjectedDefine) {
	rawDefines := make(map[string]config.DefineData)
	var valueToInject map[string]config.InjectedDefine
	var definesToInject []string

	for key, value := range defines {
		// The key must be a dot-separated identifier list
		for _, part := range strings.Split(key, ".") {
			if !lexer.IsIdentifier(part) {
				if part == key {
					log.Add(logger.Error, nil, logger.Range{}, fmt.Sprintf("The define key %q must be a valid identifier", key))
				} else {
					log.Add(logger.Error, nil, logger.Range{}, fmt.Sprintf("The define key %q contains invalid identifier %q", key, part))
				}
				continue
			}
		}

		// Allow substituting for an identifier
		if lexer.IsIdentifier(value) {
			if _, ok := lexer.Keywords[value]; !ok {
				name := value // The closure must close over a variable inside the loop
				rawDefines[key] = config.DefineData{
					DefineFunc: func(args config.DefineArgs) ast.E {
						return &ast.EIdentifier{Ref: args.FindSymbol(args.Loc, name)}
					},
				}
				continue
			}
		}

		// Parse the value as JSON
		source := logger.Source{Contents: value}
		expr, ok := parser.ParseJSON(logger.NewDeferLog(logger.DeferLogAll), source, parser.JSONOptions{})
		if !ok {
			log.Add(logger.Error, nil, logger.Range{}, fmt.Sprintf("Invalid define value (must be valid JSON syntax or a single identifier): %s", value))
			continue
		}

		var fn config.DefineFunc
		switch e := expr.Data.(type) {
		// These values are inserted inline, and can participate in constant folding
		case *ast.ENull:
			fn = func(config.DefineArgs) ast.E { return ast.ENullShared }
		case *ast.EBoolean:
			fn = func(config.DefineArgs) ast.E { return &ast.EBoolean{Value: e.Value} }
		case *ast.EString:
			fn = func(config.DefineArgs) ast.E { return &ast.EString{Value: e.Value} }
		case *ast.ENumber:
			fn = func(config.DefineArgs) ast.E { return &ast.ENumber{Value: e.Value} }

		// These values are extracted into a shared symbol reference
		case *ast.EArray, *ast.EObject:
			definesToInject = append(definesToInject, key)
			if valueToInject == nil {
				valueToInject = make(map[string]config.InjectedDefine)
			}
			valueToInject[key] = config.InjectedDefine{Source: source, Data: e, Name: key}
			continue
		}

		rawDefines[key] = config.DefineData{DefineFunc: fn}
	}

	// Sort injected defines for determinism, since the imports will be injected
	// into every file in the order that we return them from this function
	var injectedDefines []config.InjectedDefine
	if len(definesToInject) > 0 {
		injectedDefines = make([]config.InjectedDefine, len(definesToInject))
		sort.Strings(definesToInject)
		for i, key := range definesToInject {
			index := i // Capture this for the closure below
			injectedDefines[i] = valueToInject[key]
			rawDefines[key] = config.DefineData{DefineFunc: func(args config.DefineArgs) ast.E {
				return &ast.EIdentifier{Ref: args.SymbolForDefine(index)}
			}}
		}
	}

	// If we're bundling for the browser, add a special-cased define for
	// "process.env.NODE_ENV" that is "development" when not minifying and
	// "production" when minifying. This is a convention from the React world
	// that must be handled to avoid all React code crashing instantly. This
	// is only done if it's not already defined so that you can override it if
	// necessary.
	if platform == PlatformBrowser {
		if _, process := rawDefines["process"]; !process {
			if _, processEnv := rawDefines["process.env"]; !processEnv {
				if _, processEnvNodeEnv := rawDefines["process.env.NODE_ENV"]; !processEnvNodeEnv {
					var value []uint16
					if minify {
						value = lexer.StringToUTF16("production")
					} else {
						value = lexer.StringToUTF16("development")
					}
					rawDefines["process.env.NODE_ENV"] = config.DefineData{
						DefineFunc: func(args config.DefineArgs) ast.E {
							return &ast.EString{Value: value}
						},
					}
				}
			}
		}
	}

	for _, key := range pureFns {
		// The key must be a dot-separated identifier list
		for _, part := range strings.Split(key, ".") {
			if !lexer.IsIdentifier(part) {
				log.Add(logger.Error, nil, logger.Range{}, fmt.Sprintf("Invalid pure function: %q", key))
				continue
			}
		}

		// Merge with any previously-specified defines
		define := rawDefines[key]
		define.CallCanBeUnwrappedIfUnused = true
		rawDefines[key] = define
	}

	// Processing defines is expensive. Process them once here so the same object
	// can be shared between all parsers we create using these arguments.
	processed := config.ProcessDefines(rawDefines)
	return &processed, injectedDefines
}

func validatePath(log logger.Log, fs fs.FS, relPath string, pathKind string) string {
	if relPath == "" {
		return ""
	}
	absPath, ok := fs.Abs(relPath)
	if !ok {
		log.Add(logger.Error, nil, logger.Range{}, fmt.Sprintf("Invalid %s: %s", pathKind, relPath))
	}
	return absPath
}

func validateOutputExtensions(log logger.Log, outExtensions map[string]string) (js string, css string) {
	for key, value := range outExtensions {
		if !isValidExtension(value) {
			log.Add(logger.Error, nil, logger.Range{}, fmt.Sprintf("Invalid output extension: %q", value))
		}
		switch key {
		case ".js":
			js = value
		case ".css":
			css = value
		default:
			log.Add(logger.Error, nil, logger.Range{}, fmt.Sprintf("Invalid output extension: %q (valid: .css, .js)", key))
		}
	}
	return
}

func validateBannerOrFooter(log logger.Log, name string, values map[string]string) (js string, css string) {
	for key, value := range values {
		switch key {
		case "js":
			js = value
		case "css":
			css = value
		default:
			log.Add(logger.Error, nil, logger.Range{}, fmt.Sprintf("Invalid %s file type: %q (valid: css, js)", name, key))
		}
	}
	return
}

func convertLocationToPublic(loc *logger.MsgLocation) *Location {
	if loc != nil {
		return &Location{
			File:       loc.File,
			Namespace:  loc.Namespace,
			Line:       loc.Line,
			Column:     loc.Column,
			Length:     loc.Length,
			LineText:   loc.LineText,
			Suggestion: loc.Suggestion,
		}
	}
	return nil
}

func convertMessagesToPublic(kind logger.MsgKind, msgs []logger.Msg) []Message {
	var filtered []Message
	for _, msg := range msgs {
		if msg.Kind == kind {
			var notes []Note
			for _, note := range msg.Notes {
				notes = append(notes, Note{
					Text:     note.Text,
					Location: convertLocationToPublic(note.Location),
				})
			}
			filtered = append(filtered, Message{
				PluginName: msg.PluginName,
				Text:       msg.Data.Text,
				Location:   convertLocationToPublic(msg.Data.Location),
				Notes:      notes,
				Detail:     msg.Data.UserDetail,
			})
		}
	}
	return filtered
}

func convertLocationToInternal(loc *Location) *logger.MsgLocation {
	if loc != nil {
		namespace := loc.Namespace
		if namespace == "" {
			namespace = "file"
		}
		return &logger.MsgLocation{
			File:       loc.File,
			Namespace:  namespace,
			Line:       loc.Line,
			Column:     loc.Column,
			Length:     loc.Length,
			LineText:   loc.LineText,
			Suggestion: loc.Suggestion,
		}
	}
	return nil
}

func convertMessagesToInternal(msgs []logger.Msg, kind logger.MsgKind, messages []Message) []logger.Msg {
	for _, message := range messages {
		var notes []logger.MsgData
		for _, note := range message.Notes {
			notes = append(notes, logger.MsgData{
				Text:     note.Text,
				Location: convertLocationToInternal(note.Location),
			})
		}
		msgs = append(msgs, logger.Msg{
			PluginName: message.PluginName,
			Kind:       kind,
			Data: logger.MsgData{
				Text:       message.Text,
				Location:   convertLocationToInternal(message.Location),
				UserDetail: message.Detail,
			},
			Notes: notes,
		})
	}
	return msgs
}
