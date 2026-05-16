# Simply Typed

A typeful development of simple type systems with a highly parametric pipeline that enables implementating each language feature independently of other features, so that the client may assemble diverse type systems without duplicating the logic of overlapping features.

## Project Structure

### [`src/SimplyTyped/Core/`](https://github.com/LiamSchilling/simply-typed-parametric/tree/master/src/SimplyTyped/Core)

- Defines a pipeline for specifying language features and assembling features into language specifications.
- Implements the translation from a language specification into the abstract syntax of the language.
- Provides signatures for various meta-operations at the feaure level, and implements the lifting of such operations to the language level.

### [`src/SimplyTyped/Features/`](https://github.com/LiamSchilling/simply-typed-parametric/tree/master/src/SimplyTyped/Features) (client of `.../Core/`)

- Specifies various language features independently of each other.
- Implements meta-operations at the feature level according to the signatures from `Core`.

### [`src/SimplyTyped/Langs`](https://github.com/LiamSchilling/simply-typed-parametric/tree/master/src/SimplyTyped/Langs) (client of `.../Core/` and `.../Features/`)

- Assembles specifications of various languages using language features from `Features`.
- Retrieves meta-operations by applying the lifts from `Core` to implementations from `Features`.
