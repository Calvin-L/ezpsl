# EzPSL

[![Build Status](https://api.travis-ci.org/Calvin-L/ezpsl.svg?branch=master)](https://travis-ci.org/Calvin-L/ezpsl)

The easy parallel algorithm specification language.

This is a small, imperative, untyped, pseudocode-like language for describing
simple parallel algorithms.  The language "compiles" to
[TLA+](https://lamport.azurewebsites.net/tla/tla.html) so that it can be
exhaustively checked.

## Getting Started

There are no binary distributions.  You will need to install the
[Stack](https://haskellstack.org) build system and compile this tool from
source:

    git clone https://github.com/Calvin-L/ezpsl.git
    cd ezpsl
    stack build
    stack test # optional!
    cp `stack exec -- which ezpsl` .

Usage:

    ./ezpsl FILE

If the file is a `.tla` file, then the tool looks for a line of the form
`\* #include FILE.ezs` and replaces that line with the compiled TLA+ code.
If a compilation was previously done, then the old compilation is replaced with
the new one.

If the file is a `.ezs` file, then the tool prints the compiled TLA+ code on
standard out.

You can use the `-o OUT` option to control where the output gets written,
regardless of the input file extension.

For instance, to compile the Test example, run:

    ./ezpsl examples/Test.ezs

Or, to update the Test TLA+ module, run:

    ./ezpsl examples/Test.tla

## The Language

Example file:

    \* ----------------
    \* Global variables

    var v1 := 2;
    var v2 := 3;

    \* ----------------
    \* Procedures

    proc helper(x) {
        var tmp := x + 1;
        return tmp;
    }

    @entry
    proc main() {
        v1 := call helper(v2);
    }

Comments begin with `\*` and are completely ignored by the tool.

All global variables must be listed before any procedures, and local variables
within a procedure must be declared first, before any statements in the
procedure.  Procedures may be listed in any order.

The `@entry` flag indicates that a procedure is an "entry point", where threads
may start execution.  There must be one or more `@entry` procedures.

Expressions: a subset of TLA+ including integers and records.  Additionally,
the special constant `self` refers to the current thread ID.  EzPSL also has a
different set-comprehension syntax than TLA+.  For example:

 - `{ f[x] : x <- S, x > 0 }` - find all positive elements of `S` and
   construct a set by applying `f` to each one.

The TLA+ comprehensions `{x \in S : P}` and `{e : x \in S}` are not supported,
since they can be expressed using the general set-comprehension primitive.

Statements:

 - `x := e;` - assignment
 - `pick x \in set : predicate;` - nondeterministic choice.  You may omit the
   `: predicate` part, in which case the predicate defaults to `TRUE`.  If the
   set is empty or if no element matches the predicate, then the process hangs.
 - `if (e) { s } else { s }` - if-then-else
 - `while (e) { s }` - looping
 - `either { s } or { s }` - nondeterministic branching
 - `skip;` - no-op
 - `yield;` - pause the current thread and allow others to run
 - `await e;` - wait for a condition to become true.  There is an implied
   `yield` before each `await`.
 - `assert e;` - assert that the expression is true
 - `call p(arg, arg, ...);` - call a procedure and ignore its return value
 - `x := call p(arg, arg, ...);` - call a procedure and save its return value.
   Note that expressions are side-effect free; you can only call other
   procedures using a `call` statement.
 - `return e;` - return a value.  If the expression is omitted (`return;`),
   then a special undefined constant gets returned.

## Details About the TLA+ Output

EzPSL's TLA+ output _always_ requires that your specification `EXTENDS` the
following built-in modules:

 - `Sequences` (for modeling the call stack)
 - `Integers` (for comparing sequence lengths)
 - `TLC` (for constructing maps using the `:>` and `@@` operators, and for
   the `Permutations` operator)

The generated TLA+ declares the following constants:

 - `PROC_calls` for each `@entry` procedure, where `PROC` is the procedure
   name.  During model checking, each of these should be a set of model values
   used as process IDs.
 - `_Undefined`, a special token that is used for a number of purposes.  During
   model checking, it should be set to a unique model value.

The generated TLA+ declares the following variables:

 - One variable for each global `var` in the code, with the exact same names
 - A number of internal variables whose names begin with underscores:
   - `_pc` (a stack of program counter values for each process)
   - `_frames` (a stack of "call frames" for each process, containing local variables)
   - `_globalsScratch` (the actor's scratch space for globals between yield points)
   - `_ret` (the most recently returned value for each process)
   - `_actor` (the thread that is currently acting, or `_Undefined` if any
     thread may act)

The generated TLA+ declares the following operators:

 - `Init` (the initial state predicate)
 - `Next` (the next action predicate)
 - `symmetry` (a symmetry set consisting of all process IDs)
 - `vars` (a tuple of all declared variables, including internal variables)
 - `NoAssertionFailures` (an invariant stating that no process fails an
   `assert`)
 - Any number of helper operators whose names are prefixed with underscores.

**NOTE: The generated TLA+ system uses one step per statement, meaning that a
logically atomic block of code goes through multiple TLA+ states.**  However,
the global variables only change when a process yields or terminates.  Between
yield points, processes use a private snapshot of the global variables and all
changes are applied simultaneously when the process yields or terminates.

If you are curious for more details about the TLA+ output, look through the
compiled TLA+ output in the `examples` folder.

## Specifying Correctness Properties

### No Assertion Failures

The compiled TLA+ code always contains an invariant definition named
`NoAssertionFailures` asserting that no process has failed an `assert`
statement.  You can tell TLC to check `NoAssertionFailures` as an invariant to
find assertion failures.

### Global Invariants

To write a global invariant, place the invariant's definition after the
compiled output.  Even if a process makes multiple changes to the global
variables between yield points, the global variables are only modified when the
process yields.  Therefore, your invariant will never "see" intermediate states
between yield points.

### Refinement

Refinement works the same way as global invariants.  See
`examples/Refinement.tla` for an example.

### Deadlock

EzPSL generates TLA+ that supports deadlock checking.  Deadlock checking is
enabled by default in TLC.

## Comparison to PlusCal

EzPSL is similar to
[PlusCal](https://lamport.azurewebsites.net/tla/high-level-view.html#pluscal?unhideBut=hide-pluscal&unhideDiv=pluscal&back-link=tools.html#pluscal?unhideBut@EQhide-pluscal@AMPunhideDiv@EQpluscal),
another simple imperative language that can be compiled to TLA+ for model
checking.

There are a few ways in which EzPSL is better than PlusCal:

 - **EzPSL allows larger atomic blocks.**  PlusCal programs use labels to
   delimit atomic blocks, while EzPSL programs use `yield` statements.
   However, PlusCal _requires_ labels in many places, while EzPSL allows any
   number of statements---including nonterminating loops---between `yield`
   statements.  This can lead to shorter model checking times.
 - **EzPSL allows return values from procedures.**  While PlusCal can model
   return values, it is awkward to do so.  EzPSL includes them as a first-class
   primitive.  This can make some programs shorter and easier to read.
 - **EzPSL allows TLC to show an error trace when an `assert` fails.**  PlusCal
   assertions cause TLC to crash immediately.  The output shows line and column
   information, but it does not show the trace that led to the assertion
   failure.  EzPSL converts assertions into the `NoAssertionFailures` invariant
   so that TLC can show traces when they fail.

There are also ways in which PlusCal is better than EzPSL:

 - **EzPSL produces longer error traces.**  To support larger atomic blocks,
   EzPSL produces longer error traces than PlusCal when model checking finds a
   violation.  Sometimes this is an advantage; the longer error traces include
   more information about what the program did.  However, usually this is a
   disadvantage; the longer error traces take more time to understand.
 - **EzPSL is not built into the TLA+ toolbox.**  To use EzPSL you will need to
   use this command-line tool, which can be awkward and is likely to slow down
   your workflow.
