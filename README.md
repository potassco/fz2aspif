# fz2aspif
Translating flatzinc format to ASP intermediate language aspif. To be used with clingcon-3.x series.
This is based on a free flatzinc parser for GECODE, see README for details.

To produce flatzinc files from minizinc files, use the supplied clingcon translation
in folder share/clingcon.
mzn2fzn -O- --output-to-stdout -G clingcon freepizza.mzn._pizza6.dzn.mzn 
This call removes all non-standard non-linear constraints except alldistinct.
