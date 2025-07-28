- define project goal and scope
  - one line description of condition variables & their purpose in priml
    > Techniques for preventing _priority inversions_ in the use of _Condition
    > variables_ have been explored before [[Muller et al. 2023][pldi]] for use
    > in the PriML language. This work documents the beginning of implementing
    > these techniques, with the source code [hosted on GitHub][gh].
  - review past work
  - define what needed done to make one-liner a reality
    - parser
    - enforce no priority inversion at compile time
- communicate what was done
  - research
    - how to do compile time enforcement?
      - inspiration: rust borrow checker & lifetime analysis
        - sources
          - nll blog post
          - nll rfc
          - rust compiler dev book
        - how does this apply?
          - priml is gc, so no borrow checker & lifetimes don't matter for most
            values—yet _loans_ can help detect when a priority is borrowed by a
            condition variable, thus allowing detection of priority inversions
            caused by passing condition variables
  - design: three parts
    - parser add lang constructs to support cv's & related ops
      - …list constructs here from pldi
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
      - generic framework: df/
        - df
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

:::
