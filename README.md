# lean2agda

An Agda exporter for Lean 4, that produces Agda code from elaborated Lean code, written in Lean.

## How to Run

```sh
$ lake exe lean2agda <mods> [-- <decls>]
```
This exports the contents of the given Lean modules, looked up in the core library or `LEAN_PATH` (as e.g. initialized by an outer `lake env`) and their transitive dependencies.
A specific list of declarations to be exported from these modules can be given after a separating `--`.

The code was originally based on the lean4export project and retains its command line interface, although the code has been pretty much completely rewritten.

## Current status

The code works on relatively simple tasks like `lean2agda Init.Data.Nat.Gcd -- Nat.gcd_self`, but on larger tasks Agda runs out of memory when checking the single output file. Outputing separate modules would help with it.

It probably also has bugs since it's mostly a proof of concept preliminary version, although some testing has been performed.

There is no work yet to make the generated code cubical compatible.

It could also presumably be adapted relatively easily to output code for Coq or other systems.

## Limitations

Currently we have to disable Agda universe level checking via --type-in-type since Agda doesn't yet have impredicative Prop.

Also, we have to postulate Acc.rec since Agda doesn't accept it because it breaks subject reduction, and also have to postulate WellFounded.fixFEq since it depends on unfolding Acc.rec

Currently there is no support for generating multiple separate files and the generated code is not very readable: to make it more readable it would be necessary to be smarter about deduplication, run a pass on Agda's side to remove all implicits that Agda is able to successfully infer and do a few more output syntax improvements.

Lean compilation of this project is also quite slow.

## How does it work

### Lambda binder fixing

In Lean, it is allowed to pass a lambda with an implicit binder where a pi type with a non-implicit binder is-expected and so on, while in Agda binder implicitness must match.

So we go through the deduplicated expression and fix the binder types in all lambdas.

### Deduplication

In Lean, an expression can seamlessly share subexpressions using reference counting, which means that naively converting Lean expressions to another language results in exponential size blowup in general.

So we first have a pass that extracts repeated subexpressions by creating a new constant for each expression without loose bvars that appears more than once in a single constant.

We could extend it to also extract those with loose bvars but that requires to run mvar inference to figure out the types, and it seems that deduplicating those without loose bvar is enough to avoid exponential blowup on the tested Lean code.

### Unused argument erasure

This pass replaces unused arguments with "_" and can optionally erase the types of lambda arguments.

### Expression annotation

This pass annotates expression by adding mdata nodes for things that are not explicit in Lean. In particular, this includes the universe level assignments for the types of projection, and the implicitness of arguments to function applications

### Universe level specialization

Lean uses an ad-hoc mechanism where behavior changes depending on whether a universe level is 0 or not: in particular Sort n means Prop if n = 0 and Type (n - 1) otherwise, while imax l1 l2 is 0 if l2 = 0, and max l1 l2 otherwise.

Agda doesn't have any such mechanism, and so we specialize all constants into multiple versions, so that each imax second argument and Sort parameter is either always zero or always nonzero in a single version. This is similar to what the "Coq is a Lean typechecker" code did.

To perform this, we collect "level clauses", which are the OR clauses of level parameters that we need to ensure constant non-zero-ness of. We separate clauses that contain a single parameters and eliminate them from the more complex clauses, and then if there aren't less complex clauses then level parameters within them, we replace them with clauses with a single parameter.

When instantiating a constant with a level instance, we set all parameters contained in the clauses with a false/zero setting to zero, set all parameters in true/nonzero clauses to nonzero and keep the complex nonzero clauses. When translating, zero level parameters are substituted with zeros, nonzero expression are checked to be in the complex nonzero clauses.

Level expressions are normalized to be (lsuc*) max (lsuc* zero, lsuc* param u1, lsuc* param u2, ...), which is always possible once imaxes have been simplified due to our specialization.

### Inductive types

Inductive types are translated to records where possible, and to data otherwise. 

Note that Lean automatically converts indices to parameters where possible, such as in Eq, leaving them as explicit parameters of constructors, but we revert that transformation since Agda only supports having parameters be implicit arguments of constructors.

### Recursors

We translate recursors using Agda's definition by pattern matching feature, and in fact recursors are the only constants that have multiple definition patterns.

### Quotients

Quotients are currently postulated.

Using higher inductive types for them would be nicer if possible.

### Namespaces

Agda doesn't support namespaces that can be defined multiple times, so currently we simply convert the dot in namespaces to a ':' colon character and always fully qualify all namespaces.

In the future, it's possible to make all current declarations private and at the end of the module construct a module for each namespace.

This would still require to open a submodule for each imported module that defines constant in a namespace to open a namespace, since Agda doesn't have a way to open namespaces for all imported modules.
