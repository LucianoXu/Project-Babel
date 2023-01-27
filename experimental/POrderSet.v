

(** This is does not always hold. 
    Consider a sequence of shrinking real intervals. 
    Maybe we need the property of closed sets.

    It should be like this : for every topology, the closed sets form a cpo
    under supset order, and the open sets form a cpo under subset order.
*)
Definition nem_big_itsct_chain (T : iType) (c : chain (poset_type T)) : 𝒫(T)₊.
Proof.
    refine (NemSet (⋂₊ c) _).
    rewrite /NemSet.mixin_of /nem_big_itsct /nemset2set.
    destruct c => //=. rewrite /Chain.mixin_of in m.
    case (em_classic set).

    (** if [set] is empty *)
    move => H. rewrite -H. 
    have temp : { _ | set = set } = set_uni (T).
    { apply seteqP => //=. }
    rewrite {}temp. rewrite union_uni. by apply uni_neq_em.

    (** if [set] is nonempty *)
    move => H.
    have temp : { _ | set = ∅ } = set_em (T).
    { apply seteqP => //=. }
    rewrite {}temp. rewrite union_em.

    (** the main proof *)
    rewrite /big_itsct //=. rewrite nonemptyP in H.
    destruct H as [X HXin].
Abort.
