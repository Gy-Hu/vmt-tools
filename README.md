
VMT TOOLS
=========

This is a collection of tools to work with the
[VMT](https://es.fbk.eu/projects/vmt-lib) format.

Currently, the following utilities are provided (they are all written in
Python):

- `vmt.py`: parsing and printing of transition systems in the VMT format.

- `vmt2btor.py`: converter from VMT to the
  [BTOR2](https://github.com/Boolector/btor2tools) format.

- `btor2vmt.py`: converter from BTOR to VMT.

- `vmt2horn.py`: converter from VMT to
  [Constrained Horn Clauses](https://chc-comp.github.io/).

- `vmt2nuxmv.py`: converter from VMT to the SMV dialect of
  [nuXmv](https://nuxmv.fbk.eu/).

- `ltl2vmt.py`: a tool to convert LTL properties into VMT **:live-property**
  specifications (by compiling them into symbolic tableaux which are then put
  in product with the transition system).

Further converters to VMT
-------------------------

- From Constrained Horn Clauses to VMT: there's an `horn2vmt` tool that comes
  with the [IC3ia](https://es-static.fbk.eu/people/griggio/ic3ia/) model
  checker. Alternatively, there is another translator (also called
  `horn2vmt`) available on [GitHub](https://github.com/dbueno/horn2vmt).

- From nuXmv to VMT: the [nuXmv](https://nuxmv.fbk.eu/) model checker provides
  a `write_vmt_model` command.

- From [Aiger](http://fmv.jku.at/aiger/) to VMT: via nuXmv.

- From VMT to Aiger: via nuXmv.


Prerequisites
-------------

Python 3 and the
[MathSAT Python bindings](https://mathsat.fbk.eu/download.html) (available
from the MathSAT distribution).


License
-------

[GNU GPLv3](https://www.gnu.org/licenses/gpl-3.0.en.html).
