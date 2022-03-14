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

# package
## lexer
渡されたTypescriptコードを型を落としたTokenに変換する
内部で `lexer.skipTypescript` を読んで型を落とす

## parser
渡されたTokenをASTに変換する

## compiler
渡されたASTをJavascriptコードに変換する

オプションはつけないあくまでAPIに文字列として渡されたTypescriptコードを変換することだけする

`parser.Parse` の内部で `newLexer` を読んでいるので `parser.Parse` にstringでtypescriptコードを渡す

## sample code

```ts
const x: number = 1;
function square(x: number): number {
  return x ** 2;
}
```

## run
`go run main.go const x:number=1;`
