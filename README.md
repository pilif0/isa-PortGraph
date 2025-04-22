# Port Graphs

In this entry we formalise port graphs, a generalisation of ordinary graphs where ports act as connection points on nodes.

This is work in progress, and so has not yet been submitted to the Archive of Formal Proofs.

## Structure
This formalisation consists of the following sessions:
- `PortGraph` is the formalisation of port graphs, their equivalence, operations combining port graphs and a number of basic port graphs.
- `PortGraph_Export` defines the conversion of formal port graphs into a number of different formats, mainly for purposes of visualisation.

## Requirements
This formalisation is tested with Isabelle 2025, but should work with most modern versions.
The base session relies on `HOL`, plus `HOL-Library` for the formalisation of mappings.
The export session relies on the base session, plus the `Nano_JSON` entry (from the [AFP](https://www.isa-afp.org/entries/Nano_JSON.html)) and the `Show` entry (from the [AFP](https://www.isa-afp.org/entries/Show.html)).

## Installation
To use this formalisation, add it as a component to your Isabelle installation:
```
isabelle components -u PATH/TO/REPO
```
