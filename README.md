# Compositional Programming (CP)

This artifact includes the Haskell implementation of the CP language introduced in the TOPLAS paper *Compositional Programming*. It also contains several examples and three case studies written in CP. All of the CP programs in this artifact can be type-checked and run using our CP interpreter.

⚠️ This repository is not maintained. Please check our new implementation: <https://github.com/yzyzsun/CP-next>

## Docker

The image on Docker Hub can be pulled and run using the following command:

```
docker run -it yzyzsun/cp
```

## Build from Scratch

This project can be built with [Stack](https://docs.haskellstack.org/en/stable/README/).

```
stack build
stack exec cp-exe
```

## REPL

The REPL prompt is `>`

- type `:q` to quit
- type `:load` to load a file
- type `:?` for usage

```
> :load case-studies/mini-interp.cp
Typing result
: String

Evaluation result
=> "letf $f = <Lambda> in let $x = 9.0 in appf $f $x : Double = 81.0"
```

## Quick Reference

A program consists of list of declarations (separated by `;`), ended with an expression.
Like Haskell, a line comment starts with `--` and a comment block is wrapped by
`{-` and `-}`. 

* Primitive type: `Double`, `Int`, `Bool`, `String`, `List`
* Top type/value: `() : Top`
* Bottom type: `Bot`
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
* Trait: `trait [self : Person] => { age = 42 }`
* Trait type: `Trait[Person, Age]`
* Method pattern: `(Add e1 e2).eval = e1.eval + e2.eval`


## Examples

See the [examples/](./examples/) directory. All examples can be tested:

```
stack test
```

## Case Studies

All of the three case studies can be found in the [case-studies/](./case-studies/) directory:

1. Scans (in CP, Haskell, Scala, and SEDEL): [scans.cp](./case-studies/scans.cp), [scans.hs](./case-studies/scans.hs), [scans.scala](./case-studies/scans.scala), and [scans.sl](./case-studies/scans.sl)
2. Mini Interpreter: [mini-interp.cp](./case-studies/mini-interp.cp)
3. C0 Compiler: [czero.cp](./case-studies/czero.cp)
