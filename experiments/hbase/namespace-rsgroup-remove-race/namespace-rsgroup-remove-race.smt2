; Candidate: CreateNamespace validates G while it exists/has a server, but commits
; the descriptor only after a concurrent removeRSGroup has scanned namespaces.
; This is a hand-built event/state abstraction, not GraphChecker recorder output.
(set-logic QF_LIA)
(declare-const prepare Int)
(declare-const moveLastServerOut Int)
(declare-const removeNamespaceScan Int)
(declare-const removeGroupCommit Int)
(declare-const createNamespaceCommit Int)
(declare-const createTableCheck Int)
(assert (< prepare moveLastServerOut))
(assert (< moveLastServerOut removeNamespaceScan))
(assert (< removeNamespaceScan removeGroupCommit))
(assert (< removeGroupCommit createTableCheck))
(define-fun groupValidAtPrepare () Bool (< prepare moveLastServerOut))
(define-fun removeAllowed () Bool
  (and (< moveLastServerOut removeNamespaceScan)
       (< removeNamespaceScan createNamespaceCommit)))
(define-fun groupAbsentAtCreateTable () Bool
  (and removeAllowed (< removeGroupCommit createTableCheck)))
(define-fun namespaceReferencesGroupAtCreateTable () Bool
  (< createNamespaceCommit createTableCheck))
(define-fun createTableGuardThrows () Bool
  (and groupValidAtPrepare groupAbsentAtCreateTable
       namespaceReferencesGroupAtCreateTable))
(echo "Namespace commit after remove scan: inherited group guard can throw")
(push 1)
(assert (< removeGroupCommit createNamespaceCommit))
(assert createTableGuardThrows)
(check-sat)
(get-value (prepare moveLastServerOut removeNamespaceScan removeGroupCommit createNamespaceCommit createTableCheck createTableGuardThrows))
(pop 1)
(echo "Namespace commit before remove scan: remove guard prevents the later exception")
(push 1)
(assert (< createNamespaceCommit removeNamespaceScan))
(assert createTableGuardThrows)
(check-sat)
(pop 1)
