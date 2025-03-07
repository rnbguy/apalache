# Summary

[Overview](./index.md)

# Tutorials

- [Overview](./tutorials/index.md)
- [Entry-level Model Checker Tutorial](./tutorials/entry-tutorial.md)
- [Type Checker Tutorial](./tutorials/snowcat-tutorial.md)
- [Checking Pluscal specifications](./tutorials/pluscal-tutorial.md)
- [Apalache trail tips: how to check your specs faster](./tutorials/trail-tips.md)
- [Symbolic Model Checking](./tutorials/symbmc.md)
- [Specifying temporal properties and understanding counterexamples](./tutorials/temporal-properties.md)

# HOWTOs

- [Overview](HOWTOs/index.md)
- [How to write type annotations](./HOWTOs/howto-write-type-annotations.md)
- [How to use uninterpreted types](./HOWTOs/uninterpretedTypes.md)

# Apalache User Manual

- [Getting Started](./apalache/index.md)
    - [Installation](./apalache/installation/index.md)
        - [Prebuilt Packages](./apalache/installation/jvm.md)
        - [Docker](./apalache/installation/docker.md)
        - [Build from Source](./apalache/installation/source.md)
    - [Running the Tool](./apalache/running.md)
    - [An Example TLA+ Specification](./apalache/example.md)
    - [Specification Parameters](./apalache/parameters.md)
    - [Symbolic Model Checking with Apalache](./apalache/principles/index.md)
        - [Assignments and symbolic transitions](./apalache/principles/assignments.md)
        - [Folding sets and sequences](./apalache/principles/folds.md)
        - [Invariants: State, Action, Trace](./apalache/principles/invariants.md)
        - [Enumeration of counterexamples](./apalache/principles/enumeration.md)
        - [The Apalache Module](./apalache/principles/apalache-mod.md)
        - [Naturals](./apalache/principles/naturals.md)
    - [Apalache global configuration file](./apalache/config.md)
    - [TLA+ Execution Statistics](./apalache/statistics.md)
    - [Profiling Your Specification](./apalache/profiling.md)
    - [Five minutes of theory](./apalache/theory.md)
- [TLC Configuration Files](./apalache/tlc-config.md)
- [The Snowcat Type Checker](./apalache/typechecker-snowcat.md)
- [Supported Features](./apalache/features.md)
- [Obsolete: Recursive operators and functions](./apalache/principles/recursive.md)
- [Known Issues](./apalache/known-issues.md)
- [Antipatterns](./apalache/antipatterns.md)
- [TLA+ Preprocessing](./apalache/preprocessing.md)
- [Fine Tuning](./apalache/tuning.md)
- [Assignments and Symbolic Transitions in Depth](./apalache/assignments-in-depth.md)
- [KerA: kernel logic of actions](./apalache/kera.md)


# TLA+ Language Manual for Engineers

- [Introduction](./lang/index.md)
- [The standard operators of TLA+](./lang/standard-operators.md)
    - [Booleans](./lang/booleans.md)
    - [Control And Nondeterminism](./lang/control-and-nondeterminism.md)
    - [Conditionals](./lang/conditionals.md)
    - [Integers](./lang/integers.md)
    - [Sets](./lang/sets.md)
    - [Logic](./lang/logic.md)
    - [Functions](./lang/functions.md)
    - [Records](./lang/records.md)
    - [Tuples](./lang/tuples.md)
    - [Sequences](./lang/sequences.md)
    - [Bags]()
- [Apalache extensions](./lang/apalache-extensions.md)
  - [Apalache module](./lang/apalache-operators.md)
  - [Variants](./lang/variants.md)
- [User-defined operators](./lang/user-operators.md)
    - [Top-level operator definitions](./lang/user/top-level-operators.md)
    - [LET-IN definitions](./lang/user/let-in.md)
    - [Higher-order operators definitions](./lang/user/higher-order-operators.md)
    - [Anonymous operator definitions](./lang/user/lambdas.md)
    - [Local operator definitions](./lang/user/local-operators.md)
- [Modules, Extends, and Instances]()

# Idiomatic TLA+

- [Introduction](./idiomatic/index.md)
- [Keep state variables to the minimum](idiomatic/000keep-minimum-state-variables.md)
- [Update state variables with assignments](idiomatic/001assignments.md)
- [Apply primes only to state variables](idiomatic/002primes.md)
- [Use Boolean operators in actions, not `IF-THEN-ELSE`](idiomatic/007if-then-else.md)
- [Avoid sets of mixed records](./idiomatic/003record-sets.md)


# Design Documents

- [RFC 001: types and type annotations](./adr/001rfc-types.md)
- [ADR-002: types and type annotations](./adr/002adr-types.md)
- [ADR-003: transition executor (TRex)](./adr/003adr-trex.md)
- [ADR-004: code annotations](./adr/004adr-annotations.md)
- [ADR-005: JSON Serialization Format](./adr/005adr-json.md)
- [RFC-006: unit tests and property-based tests](./adr/006rfc-unit-testing.md)
- [ADR-007: restructuring](./adr/007adr-restructuring.md)
- [ADR-008: exceptions](./adr/008adr-exceptions.md)
- [ADR-009: outputs](./adr/009adr-outputs.md)
- [RFC-010: Implementation of Transition Exploration Server](./adr/010rfc-transition-explorer.md)
- [ADR-011: alternative SMT encoding using arrays](./adr/011adr-smt-arrays.md)
- [ADR-012: Adopt an ADR Template](./adr/012adr-adopt-adr-template.md)
- [ADR-013: Configuration Management Component](./adr/013adr-configuration.md)
- [ADR-014: Precise type inference for records and variants](./adr/014adr-precise-records.md)
- [ADR-015: ITF: informal trace format](./adr/015adr-trace.md)
- [ADR-016: ReTLA: Relational TLA](./adr/016adr-retla.md)
- [PDR-017: Checking temporal properties](./adr/017pdr-temporal.md)
- [ADR-018: Inlining in Apalache](./adr/018adr-inlining.md)
- [ADR-019: Harmonize changelog management](./adr/019adr-harmonize-changelog.md)
- [ADR-020: Improving membership in arenas](./adr/020adr-arenas.md)
- [RFC-021: Prioritization of Work](./adr/021rfc-prioritization.md)
- [ADR-022: Unify Configuration Management and "Pass Options"](./adr/022adr-unification-of-configs-and-options.md)
