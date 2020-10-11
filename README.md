# Compositional Programming (CP)

## Build and Run

This project can be built with
[Stack](https://docs.haskellstack.org/en/stable/README/) or
[Cabal](https://www.haskell.org/cabal/download.html).

### Stack

```
stack build
stack exec cp-exe
```

### Cabal

```
cabal sandbox init
cabal install --only-dependencies
cabal build
cabal exec cp-exe
```

## REPL

The REPL prompt is `>`

- type `:q` to quit
- type `:load` to load a file
- type `:?` for usage

```
> :load examples/case_study.cp
Typing result
: String

Evaluation result
=> "letf $f = <Lambda> in let $x = 9.0 in appf $f $x is 81.0"
```

## Quick Reference

A program consists of list of declarations (separated by `;`), ended with an expression.
Like Haskell, a line comment starts with `--` and a comment block is wrapped by
`{-` and `-}`. 

* Primitive type: `Double`, `Int`, `Bool`, `String`, `List`
* Top type/value: `() : Top`
* Bottom type/value: `undefined : Bot`
* Type annotation: `2 : Int`
* Merge: `true ,, 3`
* Intersection type: `Bool & (Int -> Int)`
* If: `if x == 0 then true else false`
* λ term: `\(x : Int) -> x + 1`
* Λ term: `/\ (A * Int) . \(x : A) -> x`
* Disjoint quantification: `forall (A*Int) . A -> A`
* Term declaration: `id A (x : A) = x`
* Application: `id @Int 2`
* Type declaration: `type Person = { name : String; male : Bool }`
* Signature declaration: `type Sig<Exp> = { Lit : Int -> Exp; Add : Exp -> Exp -> Exp }`
* Traits: `trait [self : Person] => { age = 42 }`
* Method patterns: `(Add e1 e2).eval = e1.eval + e2.eval`


## Examples 

See the [examples/](./examples/) directory. All examples can be tested:

```
stack test
```
