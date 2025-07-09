(lang dune 3.8)
(name coq-sflib)
(version 1.1.0)
(using coq 0.8)

(source (github snu-sf/sflib))
(license "BSD-2-Clause")
(authors
  "Jeehoon Kang <jeehoon.kang@kaist.ac.kr>"
  "Minki Cho <minki.cho@sf.snu.ac.kr>"
  "Jaehyung Lee <jaehyung.lee@sf.snu.ac.kr>"
  "Yeji Han <yeji.han@sf.snu.ac.kr>"
  "Gil Hur <gil.hur@sf.snu.ac.kr>"
)
(maintainers "snu-sf")

(package
 (name coq-sflib)
 (synopsis "A collection of useful Rocq lemmas and tactics")
 (description "This package provides useful Rocq lemmas and tactics, used at Seoul National University.")
 (depends
  (coq (= 8.20.0))
  ocaml
  base
  dune)
 (maintainers "snu-sf"))

(generate_opam_files true)