# EzPSL

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

    var v1 = 2;
    var v2 = 3;

    \* ----------------
    \* Procedures

    proc helper(x) {
        var tmp = x + 1;
        return tmp;
    }

    @entry
    proc main() {
        v1 = helper(v2);
    }

Comments begin with `\*` and are completely ignored by the tool.

All global variables must be listed before any procedures, and local variables
within a procedure must be declared first, before any statements in the
procedure.  Procedures may be listed in any order.

The `@entry` flag indicates that a procedure is an "entry point", where threads
may start execution.  There must be one or more `@entry` procedures.

Expressions: a subset of TLA+ including integers and records.  Additionally,
the special constant `self` refers to the current thread ID.

Statements:

 - `x := e;` - assignment
 - `if (e) { s } else { s }` - if-then-else
 - `while (e) { s }` - looping
 - `either { s } or { s }` - nondeterministic branching
 - `skip;` - no-op
 - `yield;` - pause the current thread and allow others to run
 - `await e;` - wait for a condition to become true.  There is an implied
   `yield` before each `await`.
 - `call p(arg, arg, ...)` - call a procedure and ignore its return value
 - `x := call p(arg, arg, ...)` - call a procedure and save its return value.
   Note that expressions are side-effect free; you can only call other
   procedures using a `call` statement.
 - `return e;` - return a value.  If the expression is omitted (`return;`),
   then a special undefined constant gets returned.

## Specifying Correctness Properties, and Details About the TLA+ Output

(More on this soon!)

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

There are also ways in which PlusCal is better than EzPSL:

 - **EzPSL produces longer error traces.**  To support larger atomic blocks,
   EzPSL produces longer error traces than PlusCal when model checking finds a
   violation.  Sometimes this is an advantage; the longer error traces include
   more information about what the program did.  However, usually this is a
   disadvantage; the longer error traces take more time to understand.
 - **EzPSL is not built into the TLA+ toolbox.**  To use EzPSL you will need to
   use this command-line tool, which can be awkward and is likely to slow down
   your workflow.
