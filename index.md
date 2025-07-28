# PriML Condition Variable Implementation

## Introduction

Techniques for preventing _priority inversions_ in the use of _Condition
Variables_ (CVs) have been explored before [[Muller et al. 2023][pldi]] for use
in the PriML language. This work documents the beginning of implementing these
techniques, with the source code [hosted on GitHub][gh]. To add support for
condition variables to PriML, a few different changes are needed. First, the
core operations (`wait`, `signal`, `promote`, & `newcv`) require the
appropriate syntax added to the parser. Then, keeping in line w/ PriML's core
goals, support for enforcing priority safety of CVs at compile time must be
added to the typechecker.

## Motivating examples

To guide development of CV support in PriML, the three examples written in a C-family style in _Responsive Parallelism with Synchronization_ [[2023]][pldi] were ported to PriML:

### Example 1

A simple example, showing how a CV is initialized at a given priority as
well as how the PriML compiler will raise a type error if passing a higher
priority condition variable to a lower priority thread causes a priority

(Code translated from the C-family example (Fig. 2) [[Muller et al. 2023][pldi]]).

```sml
priority high
priority low
order low < high

fun foo (cv: cv[high]) (res: int ref) =
    let val _ =
        res := !res + 1
    in
        cmd {
            signal cv (* ill-typed *)
        }
    end

main {
    cv <- newcv[high];
    res <- ref 1;
    t <- spawn[low] { foo cv res };
    sync t
}
```

### Example 2

An example of an ill-typed producer-consumer pattern program, causing a
priority inversion where the high-priority consumer may block while waiting
for a signal from the equally high-priority producer.

(Code translated from the C-family example (Fig. 3) [[Muller et al. 2023][pldi]]).

```sml
priority high
priority low
order low < high

fun prod (cv: cv[high]) (queue: int list ref) =
    let fun loop c q n =
        let val _ =
            q := n :: !q
        in
            cmd {
                signal cv;
                loop cv queue (n + 1)
            }
        end
    in
        loop cv queue 1
    end

fun cons (cv: cv[high]) (queue: ref int list) =
    let fun loop c q =
        case q of
            nil    =>
                cmd {
                    wait cv;
                    loop c q
                }
          | x::xs =>
                loop c q
    in
        loop cv queue
    end

main {
    cv <- newcv[high];
    queue <- ref nil;
    c <- spawn[high] { cons cv queue };
    p <- spawn[high] { prod cv queue }; (* ill-typed *)
    sync p
}
```

### Example 3

A well-typed example of a producer-consumer pattern program, using CV
_promotion_ to avoid a priority inversion.

(Code translated from the C-family example (Fig. 4) [[Muller et al. 2023][pldi]]).

```sml
priority high
priority low
order low < high

fun prod (cv: cv[low]) (queue: int list ref) =
    let fun loop c q n =
        let val _ =
            q := n :: !q
        in
            cmd {
                signal cv;
                loop cv queue (n + 1)
            }
        end
    in
        loop cv queue 1
    end
fun cons (cv: cv[high]) (queue: ref int list) =
    let fun loop c q =
        case q of
            nil    =>
                cmd {
                    wait cv;
                    loop c q
                }
          | x::xs =>
                loop c q
    in
        loop cv queue
    end

main {
    cv <- newcv[low];
    queue <- ref nil;
    p <- spawn[high] { prod cv queue };
    cv2 <- promote[high] cv;
    (* would now be ill-typed to spawn prod *)
    c <- spawn[high] { cons cv2 queue };
    sync c
}
```

## Related works

In planning to implement CVs & typechecker enforement of priority safety, we
were inspired by Rust's borrow checker & associated _lifetime analysis_. In
examples 2 & 3 (above), the type system outlined by Muller et al.
[[2023][pldi]] aims to prevent priority inversion via a set of typing
restrictions based on _ownership_ of CVs & relative priority of the thread the
CV operation is being done in:

> 1. To wait on a CV with priority 𝜌, a thread’s priority must be less
> 2. To wait on a CV with priority 𝜌, a thread’s priority must be less than or
>    equal to 𝜌, and
> 3. To signal a CV with priority 𝜌, a thread must own or share the CV at the
>    thread’s priority.
> 4. To pass any ownership of a CV at any priority to another thread, a thread
>    must own or share the CV at its own priority.
> 5. No thread may own or share a CV at a priority lower than that CV’s
>    priority

To enable enforcement of these typing restrictions, PriML needs to
know what thread owns any given CV, as well as when that CV is shared & what
threads it is shared with&mdash;two concepts also seen in Rust's borrow
checker.

Our research indicated that Rust's borrow checker's tracking of ownership &
lifetimes is done as a dataflow analysis done on the control flow graph
(CFG) during compile time. In this analysis, lifetimes (the region of a CFG
that a borrow lasts for) are computed first from liveness analysis of
references, then the set of in-scope _loans_ "or a statement at point P" in the
CFG are computed using gen & kill sets based on these rules given in the NLL
RFC [[Matsakis et al. 2017][nllrfc]]:

> - any loans whose region does not include P are killed;
> - if this is a borrow statement, the corresponding loan is generated;
> - if this is an assignment `lv = <rvalue>`, then any loan for some path P of
>   which `lv` is a prefix is killed.

While PriML is a garbage collected language, meaning a borrow checker & the related concept of lifetimes doesn't matter for most variable types, tracking the lifetime & loans of a condition variable allows for for using dataflow analysis to detect priority inversions.

## Overview of the Condition Variable implementation

Implementing condition variables in PriML is being done in three parts: parsing, typechecking, & dataflow analysis. An initial sketch of the implementation design is as follows:

1. perform liveness analysis using the external language AST on _all_ values
   (since we haven't done typechecking & don't yet know which ones are CVs)
2. use liveness analysis to compute lifetime constraints on CVs during
   typechecking & generate type constraints
3. perform dataflow analysis to compute loans on condition variables &
   detect priority inversions.

### Parser

The following language constructucts were added to the external language by adding the necessary tokens & parsing support:

- `v <- newcv[p]` creates a new CV at priority `p`
- `signal v` signals a CV variable named `v`
- `wait v` causes the thread to stop processing until a signal is given to the
  CV `v`
- `v' <- promote[p'] v` creates a higher priority (`p'`) handle to the same
  condition variable underlying v & stores it at `v'`

Additionally, support for specifying that an argument is a cv in a function signature (e.g. `fun foo (v: cv) = ...`) was added (although support for indicating what priority that CV type should have is not yet implemented).

### Dataflow

Next a generic dataflow analysis framework was created...

### Elab (typechecking)

---

- df
  - create generic dataflow framework
  - use df framework to assign lifetimes to cv's
- elab

- code review

  - parsing
    - parser/parse
      - …show implemented syntax for each construct from pldi
    - el
    - ast
  - df
    - graph wrapper
      - dependencies introduced by it
      - compute fn
      - dfg
        - `cfg_of_insts`, associated inductive type & their relationship to el
          datatypes
      - graph wrapper
        - dependencies introduced by it
        - exposed interface
    - TODO: apply df on el to compute loans on cv's
  - TODO: elab
    - use computed loans to check for priority inversions
  - examples
    - …examples from pldi
      - share abbreviated version
      - id changes from pldi example

- document what still needs done

  - parser
    - add support for type hints (including associated priority) on cv tags to
      functions

- conclusion?

:::{#references}

## Refererences

Stefan K. Muller, Kyle Singer, Devyn Terra Keeney, Andrew Neth, Kunal Agrawal, I-Ting Angelina Lee, and Umut A. Acar. 2023. Responsive Parallelism with Synchronization. _Proc. ACM Program. Lang. 7_, PLDI, Article 135 (June 2023), 24 pages. [https://doi.org/10.1145/3591249](https://doi.org/10.1145/3591249)

[pldi]: https://doi.org/10.1145/3591249 "Responsive Parallelism with Synchronization"
[gh]: https://github.com/smuller/PriML-lang/tree/condvar "PriML language implementation, condition variable feature branch"
[nllblog]: https://smallcultfollowing.com/babysteps/blog/2018/04/27/an-alias-based-formulation-of-the-borrow-checker/ "An alias-based formulation of the borrow checker"
[nllrfc]: https://rust-lang.github.io/rfcs/2094-nll.html "Rust RFC 2094: NLL"

:::
