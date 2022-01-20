This directory contains the Isabelle formalization used in our CAV2022 submission.
If you have Isabelle2021 (https://isabelle.in.tum.de/website-Isabelle2021) and the 
Archive of Formal Proofs 2021 (https://www.isa-afp.org) installed, then you can open 
Isabelle/jEdit to inspect our proofs.

If Isabelle2021 and the Archive of Formal Proofs 2021 are not on your machine you can 
install them as explained here:

== Installation of Isabelle and AFP on Linux ==

$ cd ~
$ mkdir CAV2022
$ cd CAV2022
$ wget https://isabelle.in.tum.de/website-Isabelle2021/dist/Isabelle2021_linux.tar.gz
$ tar zxvf Isabelle2021_linux.tar.gz
$ wget https://www.isa-afp.org/release/afp-2021-12-13.tar.gz
$ tar zxvf afp-2021-12-13.tar.gz
$ ./Isabelle2021/bin/isabelle components -u ./afp-2021-12-13/thys/
$ ./Isabelle2021/bin/isabelle jedit


The last command starts Isabelle/jEdit which is Isabelle's Prover IDE.
In Isabelle/jEdit under File>Open you can  open the various .thy files in our 
reproducibility package to inspect our proofs.
