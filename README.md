# Forked from GeoCoq
A forked formalization of geometry in Coq by Goyet Christopher

Trying to make a more usable version of Geocoq in practice, with :
- the fewest tactics as possible,
- explicit and readable proofs (especially without auto tactics),
- faster compilation (another reason to avoid auto tactics),
- short files and sorting lemmas by same utility/similarity/goal/aim, 
- changing the names of lemmas to make them more understandable and recognizable,
- as many lemmas as possible to :
  - simplify the use for everyone (without having to know the whole library by heart ...)
  - have a large choice of constructors, to avoid having to go back to the definition
  - banning unfold tactic to have a code that is as independent as possible from the choice of definitions and as maintainable as possible. 

Goyet Christopher

# master branch : GeoCoq

This library contains a formalization of geometry using the Coq proof assistant. It contains both proofs about the foundations of geometry and high-level proofs in the same style as in high-school.

Details and installation instructions can be found here:
http://geocoq.github.io/GeoCoq/

Bug reports:
https://github.com/GeoCoq/GeoCoq/issues

Mailing list:
https://groups.google.com/forum/?hl=fr#!forum/geocoq

[![Build Status](https://travis-ci.org/GeoCoq/GeoCoq.svg?branch=master)](https://travis-ci.org/GeoCoq/GeoCoq)
