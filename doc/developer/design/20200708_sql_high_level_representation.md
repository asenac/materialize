# High level representation for SQL queries

## Summary

<!--
// Brief, high-level overview. A few sentences long.
// Be sure to capture the customer impact - framing this as a release note may be useful.
-->

The present docuemnt proposes the introduction of a new high-level representation for SQL queries for
replacing the current `HirRelationExpr` enum.

The proposal in this document is based on the Query Graph Model representation first introduced in
[H. Pirahesh et al](http://projectsweb.cs.washington.edu/research/projects/db/weld/pirahesh-starburst-92.pdf).

## Goals

<!--
// Enumerate the concrete goals that are in scope for the project.
-->

## Non-Goals

<!--
// Enumerate potential goals that are explicitly out of scope for the project
// ie. what could we do or what do we want to do in the future - but are not doing now
-->

## Description

<!--
// Describe the approach in detail. If there is no clear frontrunner, feel free to list all approaches in alternatives.
// If applicable, be sure to call out any new testing/validation that will be required
-->

In QGM, a query, as its name implies, is represented as a graph model. This graph will be represented
by a `Model` struct, that will be declated as follows:

```rust
    struct Model<'a> {
        top_box: BoxId,
        boxes: HashMap<BoxId, Box<QueryBox<'a>>>,
        quantifiers: HashMap<QuantifierId, Box<Quantifier>>,
    }
```

The graph has a top level box, which is the entry point of the query. In this proposal, all boxes and quantifiers
are owned by the model and are referenced by its unique identifier.

Boxes represent high-level conceptual operators, ie. they don't correspond to any execution strategy. Each box
has a set of input quantifiers, which describe the semantics of how the underlying boxes will be accessed.

The following snippet contains the definition of the different types of operators and quantifiers. Since both
all type of boxes and quantifiers have elements in common, both boxes and quantifiers are not directly
represented as enum, but as struct with an enum type, containing the per-type specific members.

```rust

    type QuantifierId = usize;
    type BoxId = usize;
    type QuantifierSet = BTreeSet<QuantifierId>;

    struct QueryBox<'a> {
        /// the model the box belongs to
        model: &'a Model<'a>,
        /// uniquely identifies the box within the model
        id: BoxId,
        /// the type of the box
        box_type: BoxType,
        /// the projection of the box
        columns: Vec<Column>,
        /// the input quantifiers of the box
        quantifiers: QuantifierSet,
        /// quantifiers ranging over this box
        ranging_quantifiers: QuantifierSet,
    }

    enum BoxType {
        BaseTable(BaseTable),
        Except,
        Grouping(Grouping),
        Intersect,
        OuterJoin(OuterJoin),
        Select(Select),
        TableFunction(TableFunction),
        Union,
        Values(Values),
    }

    struct Quantifier {
        /// uniquely identifiers the quantifier within the model
        id: QuantifierId,
        /// the type of the quantifier
        quantifier_type: QuantifierType,
        /// the input box of this quantifier
        input_box: BoxId,
        /// the box that owns this quantifier
        parent_box: BoxId,
        /// alias for name resolution purposes
        alias: Option<String>,
    }

    enum QuantifierType {
        All,
        Any,
        Existential,
        Foreach,
        PreservedForeach,
        Scalar,
    }
```

Note that input quantifiers are logically owned by a single box, but there may be several quantifiers ranging
over the same box. That is the case, for example, for base tables, views or CTEs, either explicit CTEs used in
the query or discovered via some query transformation.

As shown above, there aren't many different types of operators, since QGM is meant to be a representation for
query normalization. The core operator is represented by the `Select` box, which represents a whole query block
(sub-block).

```rust
    struct Select {
        predicates: Vec<Box<Expr>>,
        order_key: Option<Vec<Box<Expr>>>,
        limit: Option<Expr>,
        offset: Option<Expr>,
    }
```

There a few subtle constraints that are not explicit in the representation above:

* `BaseTable`, `TableFunction` and `Values` cannot have input quantifiers.
* `Union`, `Except` and `Intersect` can only have input quantifiers of type `Foreach`.
* Subquery quantifiers (`All`, `Any`, `Existential` and `Scalar` are only allowed in `Select` boxes.
* `Grouping` must have a single input quantifier of type `Foreach` ranging over a `Select` box.
* `OuterJoin` must have at leat an input quantifier of type `PreservedForeach`. The remaining onee, if any, must
  be of type `Foreach`. An `OuterJoin` with all `PreservedForeach` input quantifiers represents a `FULL OUTER JOIN`.
  Note: temporarily during the generation of the query model we could allow subquery quantifiers in `OuterJoin` boxes for
  subqueries in the `ON`-clause of the outer join, but should push down the subquery to the non-preserving side.
  Note 2: In QGM there is no distiction between a `LEFT JOIN` and a `RIGHT JOIN`, since that's a concept that belongs
  only in the AST.

Some of the constraints above are just conventions for making query transformation easier due to having to cover
fewer cases. The rest are just constructions that don't make sense semantically speaking.

### Notes on expression representation

### Examples

This section includes examples of how some queries look like in QGM. This visual representation will be generated
from the representation decribed in the previou section. Note that having a visual way of representing the query
is very helpful during query transformation development/troubleshooting.

#### Simple `SELECT *`

![Simple SELECT *](qgm/simple-select-star.svg)

#### Simple `GROUP BY`

![Simple GROUP BY](qgm/simple-group-by.svg)


#### `GROUP BY + HAVING`

![GROUP BY + HAVING](qgm/simple-group-by-having.svg)

Note that the having filter is just a regular predicate on the `Select` box ranging over the `Grouping` box.

#### Comma join

![Simple comma join](qgm/simple-comma-join.svg)

#### Inner join

![Simple inner join](qgm/simple-inner-join.svg)

Note that the inner join above is semantically equivalent to the comma join in the previous example. Boxes 1 and 2
represent the binary inner joins in the query, but they can be squashed into box 0, without altering the results of
the query. In fact, the normalization step will simplify this query leaving it exactly as the one in the example above:

![Simple inner join after normalization](qgm/simple-inner-join-after-normalization.svg)

#### Left join

#### Cross join

#### CTEs

![Simple CTE](qgm/simple-cte.svg)

Quantifiers 2 and 3 are ranging over the same box, which represents the CTE. Box 2 doesn't alter the results of
box 0, but just adds aliases for the columns, for name resolution purposes. Normalization will get rid of all
the intermediate `Select` boxes, leaving the query as follows:

![Simple CTE after normalization](qgm/simple-cte-after-normalization.svg)

### Name resolution

As shown above, the query graph already contains almost all the information needed for name resoltion. Since the
query graph is built in a bottom-up manner, we can use the input quantifier for resolving names within the
current part of the query being processed.

To be continued...

### Distinctness and unique keys

### Query model transformations

## Alternatives

<!--
// Similar to the Description section. List of alternative approaches considered, pros/cons or why they were not chosen
-->

* QGM with interior mutability, shared pointers and so on as implemented [here](https://github.com/asenac/rust-sql).
* Relational algebra representation

## Open questions

<!--
// Anything currently unanswered that needs specific focus. This section may be expanded during the doc meeting as
// other unknowns are pointed out.
// These questions may be technical, product, or anything in-between.
-->
