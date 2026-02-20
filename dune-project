(lang dune 3.8)
(name coq-sflib)
(version 2.1.0)
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
(maintainers "yeji.han@sf.snu.ac.kr")

(package
 (name coq-sflib)
 (synopsis "A collection of useful Rocq lemmas and tactics")
 (description "This package provides useful Rocq lemmas and tactics for proof automation and rewriting.")
 (depends
  (coq-core (>= 9.0))
  rocq-stdlib
  (dune (>= 3.8)))
 (maintainers "yeji.han@sf.snu.ac.kr"))

(generate_opam_files true)
