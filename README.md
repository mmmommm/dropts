# dropts

quote from esbuild
only drop type definition and transform enum jsx etc...

## function dependency
input -> lexer -> parser -> compiler -> output
// SourceCode ~~Scanner~~> Tokens ~~Parser~~> AST ~~Emitter~~> JavaScript

// NewLexer -> newParser -> Parse -> parseFile -> maybeParseFile -> scanAllDependencies -> ScanBundle -> Compile -> buildImpl -> Build

# memo
parseの処理でtsを落としてASTに変換してそれをcompileImplに渡してASTをjsに変換する、CompileでcompileImplをラップして外部公開

<!-- ScanBundleの処理は必要ないと思うのでparseFileで返したParseResultをそのままcompileImplに渡す -->

parseFileでの結果は parseArgsの `args.results` に入る、scannerに入れられてresultの値を各種scannerに実装されているメソッドで加工している、
scannerに渡されたparseResultは各種scanの過程を経て `ScanBundle` で呼ばれてcompileの処理に渡される

# impl memo
playgroundで特定の文字列を受け取ってcompileした結果を返すapiとして提供するのであれば、stringで引数を取ってそれを `lexer, parser, compiler` の順に渡すようにすれば問題ない。

esbuildのようにcliなどでファイル単位で渡したものを全てcompileしてファイル依存解消してminifyして返すようにするためには設計考える必要あり。

input ~~Lexer~~> Tokens ~~Parser~~> AST ~~Compiler~~> Javascript
