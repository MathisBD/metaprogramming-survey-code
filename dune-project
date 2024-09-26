(lang dune 3.16)

(using coq 0.9)

(name coq-metaprogramming)

; The .opam file is regenerated each time you call dune build.
; To manually regenerate the .opam file, run :
; $ dune build coq-metaprogramming.opam

(generate_opam_files true)

(package
 (name coq-metaprogramming)
 (maintainers "Mathis Bouverot-Dupuis (mathis.bouverot@ens.psl.eu)")
 (authors "Mathis Bouverot-Dupuis")
 (homepage "https://github.com/MathisBD/coq-metaprogramming")
 (bug_reports "https://github.com/MathisBD/coq-metaprogramming/issues")
 (synopsis "Comparison of the different metaprogramming languages for Coq")
 (depends
  (coq
   (= 8.20.0))
  (coq-elpi
   (>= 2.2.3))))
