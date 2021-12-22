# dropts

quote from esbuild
only drop type definition and transform enum jsx etc...

## function dependency
input -> lexer -> parser -> scanner -> compiler -> output

NewLexer -> newParser -> Parse -> parseFile -> maybeParseFile -> scanAllDependencies -> ScanBundle -> Compile -> buildImpl -> Build
