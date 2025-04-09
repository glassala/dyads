import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Data.Fintype.Basic
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-
    Part 1 : "2"
-/

instance plus : Add (Bool) where add x y := xor x y -- + is XOR.

/--
    Boolean truth values form a monoid under AND. They do not
    form a group under this operation, however, because true is its
    identity, and ∄x ∈ {true, false} such that x ∧ false = true. That is,
    false has no inverse under AND.
-/
instance and_monoid : Monoid Bool where
    mul := and
    mul_assoc := Bool.and_assoc
    one := true
    one_mul := by simp
    mul_one := by simp
/--
    Similarly, Boolean truth values form a monoid but not a group under OR,
    because false is its identity element, meaning true has no inverse w/r/t OR.
-/
instance or_monoid : Monoid Bool where
    mul := or
    mul_assoc := Bool.or_assoc
    one := false
    one_mul := by aesop
    mul_one := by
        simp_all [Bool.false_or]
        constructor
        case left =>
            aesop
        case right =>
            aesop
/--
    Boolean truth values form a semiring with OR as + and AND as *. A semiring
    is a set and some + and * operations defined on elements of that set,
    such that * is a monoid and + is a commutative monoid. The set has to have
    a "0" element which is both the additive identity and the multiplicative
    annihilator, as well as a "1" element which is the multiplicative identity.
    "*" does not have to be commutative and neither "+" nor "\*" needs to have inverses.
-/
instance : Semiring Bool where
    zero := false -- additive identity / multiplicative annihilator
    one := true -- multiplicative identity
    add := or -- the + operation
    add_assoc := Bool.or_assoc -- + is associative.
    zero_add := by aesop -- left additive identity
    add_zero := by -- right additive identity
        simp_all [Bool.false_or]
        constructor
        case left =>
            aesop
        case right =>
            aesop
    add_comm := Bool.or_comm -- + is commutative
    mul := and -- the * operation
    mul_assoc := Bool.and_assoc -- * is associative.
    one_mul := by simp -- left multiplicative identity
    mul_one := by simp -- right multiplicative identity
    zero_mul := by simp -- left multiplicative annihilation
    mul_zero := by simp -- right multiplicative annihilation
    left_distrib := Bool.and_or_distrib_left -- * distributes over + from left
    right_distrib := Bool.and_or_distrib_right -- * distributes over * from left
    nsmul := λ n x ↦ n != 0 && x -- scalar multiplication by iterated +
    nsmul_succ := by -- scalar multiplication works "as expected"
        intro n x
        simp_all only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        induction n with
            | zero =>
                simp
                apply Bool.false_or
            | succ n =>
                simp
                have h : x = or x x := by
                    simp
                apply h
    natCast := λ n ↦ n != 0
    natCast_succ := by
        simp_all
        intro n
        cases (n != 0)
        case false =>
            aesop
        case true =>
            aesop
/--
    "Boolean scalar multiplication" by a natural number. Necessary
    in order to construct an additive monoid from XOR.
-/
def ns_bool : ℕ -> Bool -> Bool := λ n x ↦
    match (n % 2 == 0) with
        | true => false
        | false => x
/--
    A more elegant formulation of the Boolean scalar multiplication
    that I only thought up after I had written my AddMonoid proofs,
    but before I learned about nsmulRec and zsmulRec. So it goes.
-/
def ns_bool' : ℕ -> Bool -> Bool := λ n x ↦ (n % 2 == 1) && x
/--
    Any Boolean scaled by 0 is false.
-/
theorem ns_zero_false (x : Bool) :
    ns_bool 0 x = false := by
        rfl
/--
    Scaling a Boolean by an even number always results in a "false."
-/
theorem ns_even_false (n : ℕ) (x : Bool) (p : n % 2 = 0) :
    ns_bool n x = false := by
        unfold ns_bool
        simp_all [p]
/--
    Scaling a Boolean by an odd number amounts to the identity function.
-/
def ns_odd_id (n : ℕ) (x : Bool) (p : n % 2 = 1) :
    ns_bool n x = x := by
        unfold ns_bool
        simp_all [p]
/--
    False scaled by any number will remain false.
-/
theorem ns_false_false (n : ℕ) :
    ns_bool n false = false := by
        unfold ns_bool
        aesop
/--
    If a true value scaled by n is still true, it will be
    false if scaled by n + 1.
-/
theorem ns_true_succ_false (n : ℕ) :
    ns_bool n true = true → ns_bool (n + 1) true = false := by
        intro h
        unfold ns_bool at *
        split at h
        · contradiction
        ·
            rw [Nat.succ_mod_two_eq_zero_iff.mpr]
            case h_2 => rfl
            case h_2 => simp_all [Nat.mod_two_eq_zero_or_one]
/--
    A ⊕ A for some predicate A is always false.
-/
theorem xor_self_false (a : Bool) : xor a a = false := by simp
/--
    A ⊕ A is always false, and as such A ⊕ A scaled by any natural number
    is false.
-/
theorem null_scale_law (n : ℕ) (x : Bool) :
    ns_bool n (xor x x) = false := by
        simp
        have mod_two_cases : n % 2 = 0 ∨ n % 2 = 1 := by
            exact Nat.mod_two_eq_zero_or_one n
        cases mod_two_cases with
            | inl h_zero =>
                unfold ns_bool
                aesop
            | inr h_one =>
                unfold ns_bool
                aesop
/--
    Certifies that scalar multiplication "works as expected"
    for an additive monoid.
-/
theorem natural_scale_law (n : ℕ) (x : Bool) :
    ns_bool (n + 1) x = xor (ns_bool n x) x := by
        have mod_two_cases : n % 2 = 0 ∨ n % 2 = 1 := by
            exact Nat.mod_two_eq_zero_or_one n
        cases mod_two_cases with
            | inl h_zero =>
                simp only [ns_bool]
                rw [h_zero]
                simp only [beq_self_eq_true, cond_true]
                rw [Nat.add_mod, h_zero]
                aesop
            | inr h_one =>
                simp only [ns_bool]
                rw [h_one]
                rw [Nat.add_mod, h_one]
                rw [Nat.add_comm, Nat.add_mod]
                simp only [
                    Nat.add_mod,
                    Nat.mod_self,
                    zero_add,
                    beq_self_eq_true,
                    cond_true
                ]
                aesop
/--
    Boolean truth values form an additive monoid under
    the ⊕ (XOR) operation.
-/
instance : AddMonoid Bool where
    add := xor
    add_assoc := by apply Bool.xor_assoc
    zero := false
    zero_add := by simp
    add_zero := by simp
    nsmul := ns_bool
    nsmul_succ := natural_scale_law
/--
    Boolean truth values have both unary negation and subtraction.
    Here, unary negation is the identity and subtraction is the same
    as addition (⊕). As such, each truth value is its own inverse,
    so ⊕ is a group. Since ⊕ is commutative, that group is
    an abelian (commutative) group.
-/
instance : AddCommGroup Bool where
    add := xor
    add_assoc := by apply Bool.xor_assoc
    zero := false
    zero_add := by simp
    add_zero := by simp
    nsmul := ns_bool
    nsmul_succ := natural_scale_law
    neg := id
    sub := xor
    zsmul := zsmulRec
    sub_eq_add_neg := by aesop
    neg_add_cancel := Bool.xor_self
    add_comm := Bool.xor_comm
/--
    Boolean truth values also form a ring, with ⊕ as + and ∧ as *. In a ring,
    + is an abelian (commutative) group, * is a monoid, and * distributes
    over + (on both the left and right).
-/
instance : Ring Bool where
    zero := false -- Identity
    one := true
    add := xor
    mul := and
    add_assoc := by apply Bool.xor_assoc
    zero_add := by simp
    add_zero := by simp
    add_comm := Bool.xor_comm
    mul_assoc := by apply Bool.and_assoc
    zero_mul := by simp
    mul_zero := by simp
    one_mul := by simp
    mul_one := by simp
    nsmul := nsmulRec
    zsmul := zsmulRec
    neg_add_cancel := Bool.xor_self
    left_distrib := Bool.and_xor_distrib_left
    right_distrib := Bool.and_xor_distrib_right
/--
    The idempotence of the two-element algebra (that is, the fact that
    x ∧ x = x for both true and false) motivates the idea of a Boolean ring,
    which is a ring where x² = x for all x in the ring's underlying set.
-/
instance archetype_definer : BooleanRing Bool where
    isIdempotentElem := Bool.and_self
/--
    We can define a strong ordering (<) on Bool, taking false < true.
-/
instance : LT Bool  where
    lt := λ x y ↦ (x.toInt < y.toInt)
/--
    We can define a weak ordering (<=) on Bool, taking false < true.
-/
instance : LE Bool where
    le := λ x y ↦ (x.toInt <= y.toInt)
/--
    The AND operation serves as a minimum, if we take false < true.
-/
instance : Min Bool where
    min := λ x y ↦ x && y
/--
    The OR operation serves as a maximum, if we take false < true.
-/
instance : Max Bool where
    max := λ x y ↦ x || y
/--
    The set of Boolean truth values is totally ordered. Any totally ordered set
    is also partially ordered.
-/
instance : LinearOrder Bool where
    le := λ x y ↦ match x, y with
        | false, false => true
        | false, true => true
        | true, false => false
        | true, true => true
    lt := λ x y ↦ match x, y with
        | false, false => false
        | false, true => true
        | true, false => false
        | true, true => false
    min := λ x ↦ λ y ↦ x && y
    min_def := by simp
    max := λ x ↦ λ y ↦ x || y
    max_def := by simp
    le_refl := by simp
    le_trans := by simp
    le_antisymm := by simp
    le_total := by simp
    decidableLE := λ x y ↦
        match x, y with
            | false, _ => isTrue (by aesop)
            | true, false => isFalse (by simp)
            | true, true => isTrue (by simp)
    lt_iff_le_not_le := by aesop
/-
    Naturally, the Boolean truth values give rise to a Boolean lattice,
    also called a Boolean algebra. "An algebra" (as opposed to simply "algebra")
    in this setting is the same as "a lattice," or one can say that these are names
    for two ways of looking at the same structure.

    That is, "lattice" is a way of looking at a set through a partial order relation
    imposed on it: a partially ordered set is a lattice if each two-element
    subset of that set has a "meet," a greatest lower bound which generalizes
    AND/set intersection, and a "join," a least upper bound which generalizes
    OR/set union.

    On the other hand, "algebra" emphasizes that some set S with a defined (associative
    and commutative) meet ⊓ and (associative and commutative) join ⊔ satisfies the
    following properties for all x, y ∈ S:

    1. x ⊓ (x ⊔ y) = x
    2. x ⊔ (x ⊓ y) = x
    3. x ⊓ x = x
    4. x ⊔ x = x

    Any Boolean algebra with ∧ and ∨ corresponds to
    a Boolean ring with ∧ and ⊕. The two-element Boolean algebra is far from the only
    Boolean algebra. Boolean algebras generalize the subset inclusion lattice of
    a power set.

    The power set of the empty set trivially gives rise to a Boolean algebra:
    Since the power set of the empty set ∅ has 1 element, that being ∅, ∅ is
    supremum, infimum, as well as the set's only element's complement, all in one.

    The two-element algebra on truth values is a special case of the subset
    inclusion algebra of the power set of a singleton set. The ∧ operation maps to
    set intersection ∩ and the ∨ operation maps to set union ∪.

    Another way to impose the Boolean
    algebra on a two-element set is to consider the set {∅, {∅}} under intersection
    and union. ∅ ⊆ ∅, and ∅ ⊆ {∅}, but {∅} ⊈ ∅. Moreover, ∅ ∪ {∅} ⊆ {∅} and
    ∅ ∩ {∅} ⊆ ∅.
-/
/--
    The archetypal Boolean algebra. A Boolean algebra is a partially ordered set
    with a commutative binary meet operation (AND) and a commutative binary join
    operation (OR), along with a complement for each element in its set.
    The set must also be bounded such that there is a maximum element (true)
    and a minimal element (false). In addition, the meet operation and the join
    operation must distribute over one another. For this reason a Boolean algebra
    can also be described as a complemented bounded distributive lattice.
-/
instance : BooleanAlgebra Bool where
    compl := λ x ↦ ¬x
    le := λ x y ↦ match x, y with
        | false, false => true
        | false, true => true
        | true, false => false
        | true, true => true
    lt := λ x y ↦ match x, y with
        | false, false => false
        | false, true => true
        | true, false => false
        | true, true => false
    lt_iff_le_not_le := by aesop
    le_refl := by simp
    le_trans := by simp
    le_antisymm := by simp
    inf := λ x ↦ λ y ↦ x && y
    inf_le_left := by simp
    inf_le_right := by simp
    le_inf := by simp
    sup := λ x ↦ λ y ↦ x || y
    le_sup_left := by simp
    le_sup_right := by simp
    sup_le := by simp
    le_sup_inf := by simp
    le_top := by simp
    bot_le := by simp
    inf_compl_le_bot := by simp
    top_le_sup_compl := by simp
    /-
        The above construction really puts the "automated" in automated theorem prover.
        It is sensible that Lean would be able to figure out that the Bool type is a
        Boolean algebra. It is literally in the name, which is to say that the latter
        is in no small part a generalization of the former.

        How one defines the operations/relations themselves also matters for how well
        Lean can "figure something out on its own." Since, for a two-element set, one
        can simply list out the results of the 4 possible ways to put them together,
        it is feasible to prove things by simply exhausting a
        pattern-matching "truth table."
    -/


/--
    The Boolean type is isomorphic to the integers modulo 2.
-/
def bool_iso_mod_two : Bool ≃ ZMod 2 where
    toFun := λ x ↦ match x with
        | true => 1
        | false => 0
    invFun := λ n ↦ match n with
        | 1 => true
        | 0 => false
    left_inv := λ x ↦ by cases x <;> rfl -- "method by exhaustion"
    right_inv := λ x ↦ (by cases x; aesop)


-- Truth and parity --

/-
    All instances of "one or the other" give rise to the same structures,
    and they only have to be given names.

    Another way of saying this is that the two-element Boolean algebra
    is still a two-element Boolean algebra on any two-element set.
    Anyone who can find their way to a Lean repository on GitHub
    likely intuitively understands the isomorphism between {true, false}
    and {1, 0} because its consequences are ubiquitous to everything
    related to the computer.

    It may or may not be so obvious that this property generalizes:
    Since the property of parity of an integer, i.e. whether it is odd or even,
    is equivalent to its remainder when divided by 2 being 1 or 0 respectively,
    the same structures emerge from odd and even which emerge from true and false.
    We can encode these structures through polynomial congruences modulo 2.

    Which of the two elements
    within a two-element set is which is irrelevant. Or, one could say it's a
    matter of linguistics and not math. If all instances of "odd" and "even" in
    language were suddenly swapped, and everyone began insisting that numbers n where
    (n % 2 == 1) were even, and numbers m where (m % 2 == 0) were odd, then nothing
    would be fundamentally different about mathematics.

    It would be valid to define a "MirrorWorldBool"
    type where we treat false like true and true like false, but this would
    be both confusing and annoying. As such, we will abstract true and false,
    1 and 0, odd and even, singleton and empty, and so on, into the meaningless
    A and B.
-/
/--
    Abstracted "one or the other" Dyad type.
-/
inductive Dyad
    | A -- Odd/1/true by convention.
    | B -- Even/0/false by convention.
deriving DecidableEq

open Dyad

/--
    Corresponds to XOR, along with addition modulo 2.
-/
instance : Add Dyad where add x y :=
    match x, y with
        | B, _ => y
        | _, B => x
        | A, A => B
/--
    Corresponds to AND, along with multiplication modulo 2.
-/
instance : Mul Dyad where mul x y :=
    match x, y with
        | A, _ => y
        | _, A => x
        | B, B => B
/--
    Less than or equal to relation. Corresponds to (¬x ∨ y), i.e.
    logical implication, along with the polynomial xy + x + 1 modulo 2.
-/
instance : LE Dyad where
    le x y := match x, y with
        | A, A => true
        | A, B => false
        | B, A => true
        | B, B => true
/--
    Less than relation. Corresponds to (¬x ∧ y), i.e. converse
    non-implication, along with the polynomial xy + y modulo 2.
-/
instance : LT Dyad where
    lt x y := match x, y with
        | A, A => false
        | A, B => false
        | B, A => true
        | B, B => false
/--
    The AND operation serves as a minimum.
-/
instance : Min Dyad where
    min x y := x * y
/--
    The OR operation serves as a maximum.
-/
instance : Max Dyad where
    max x y := (x * y) + x + y
/-
    We can take the same linear order applied to Bool and apply it here.
-/
instance : LinearOrder Dyad where
    min := λ x ↦ λ y ↦ min x y
    min_def := λ x y => by
        cases x <;> cases y <;> simp_all [LE.le, LT.lt]
        rfl; rfl; rfl; rfl
    max := λ x ↦ λ y ↦ max x y
    max_def := λ x y => by
        cases x <;> cases y <;> simp_all [LE.le, LT.lt]
        rfl; rfl; rfl; rfl
    le_refl := λ x => by
        cases x <;> rfl
    le_antisymm := λ x y => by
        cases x <;> cases y <;> simp_all [LE.le]
    le_trans := λ x y z => by
        cases x <;> cases y <;> cases z <;> simp_all [LE.le]
    lt_iff_le_not_le := λ x y => by
        cases x <;> cases y <;> simp_all [LE.le, LT.lt]
    le_total := λ x y => by
        cases x <;> cases y <;> simp [LE.le]
    decidableLE := λ x y ↦
        match x, y with
            | A, A => isTrue (by simp [LE.le])
            | A, B => isFalse (by simp [LE.le])
            | B, A => isTrue (by simp [LE.le])
            | B, B => isTrue (by simp [LE.le])
/--
    The Dyad type has 2 elements.
-/
instance : Fintype Dyad where
    elems := [A, B].toFinset
    complete := λ x => by cases x <;> simp
/-
    Nullary operations / constants / P ≡ x (mod 2)
-/
/--
    1 : Nullary : ⊤ :  P ≡ 1 (mod 2)
-/
def a : Dyad := A
/--
    2 : Nullary : constant ⊥ : P(x) ≡ 0 (mod 2)
-/
def b : Dyad := B
/-
    Unary operations / P(x) ≡ y (mod 2)
-/
/--
    1 : Unary : ⊤ : P(x) ≡ 1 (mod 2). Every constant can be rewritten as a
    function of an arbitrary number of arguments (which are all discarded).
-/
def a' : Dyad -> Dyad :=
    λ x ↦ A
/--
    2 : Unary : ⊤ : P(x) ≡ 1 (mod 2). Constant functions with different
    numbers of arguments have different types.
-/
def b' : Dyad -> Dyad :=
    λ x ↦ B
/--
    3 : Unary : id : P(x) ≡ x (mod 2). The identity function.
-/
def same : Dyad -> Dyad :=
    λ x ↦ x
/--
    4 : Unary : NOT (¬) : P(x) ≡ x + 1 (mod 2). The complement function.
-/
def other : Dyad -> Dyad :=
    λ x ↦ x + A
/-
    Binary operations / P(x, y) ≡ z (mod 2)
-/
/--
    1 : Binary : ⊤ : P(x, y) ≡ 1 (mod 2)
-/
def a'' : Dyad -> Dyad -> Dyad :=
    λ x y ↦ A
/--
    2 : Binary : ⊥ : P(x, y) ≡ 0 (mod 2)
-/
def b'' : Dyad -> Dyad -> Dyad :=
    λ x y ↦ B
/--
    3 : Binary : "project first argument" : P(x, y) ≡ x (mod 2). Generalizes
    unary identity for x, discarding y.
-/
def first : Dyad -> Dyad -> Dyad :=
    λ x ↦ λ y ↦ x
/--
    4 : Binary : "project second argument" : P(x, y) ≡ y (mod 2). Generalizes
    unary identity for y, discarding x.
-/
def second : Dyad -> Dyad -> Dyad :=
    λ x ↦ λ y ↦ y
/--
    5 : Binary : "project first argument's complement" : P (x, y) ≡ x + 1 (mod 2).
    Generalizes unary NOT, taking ¬x and discarding y.
-/
def first_other : Dyad -> Dyad -> Dyad :=
    λ x ↦ λ y ↦ x + A
/--
    6 : Binary : "project first argument's complement" : P (x, y) ≡ y + 1 (mod 2).
    Generalizes unary NOT, taking ¬y and discarding x.
-/
def second_other : Dyad -> Dyad -> Dyad :=
    λ x ↦ λ y ↦ y + A
/--
    7 : Binary : XOR : P(x, y) ≡ x + y (mod 2)
-/
def unlike : Dyad -> Dyad -> Dyad :=
    λ x ↦ λ y ↦ x + y
/--
    8 : Binary : NXOR : P(x, y) ≡ x + y + 1 (mod 2)
-/
def alike : Dyad -> Dyad -> Dyad :=
    λ x ↦ λ y ↦ x + y + A
/--
    9 : Binary : AND : P(x, y) ≡ xy (mod 2)
-/
def aligned : Dyad -> Dyad -> Dyad :=
    λ x ↦ λ y ↦ x * y
/--
    10 : Binary : NAND : P(x, y) ≡ xy + 1 (mod 2)
-/
def unaligned : Dyad -> Dyad -> Dyad :=
    λ x ↦ λ y ↦ (x * y) + A
/--
    11 : Binary : α -> β : P(x, y) ≡ xy + x + 1 (mod 2)
-/
def indicating : Dyad -> Dyad -> Dyad :=
    λ x ↦ λ y ↦ (x * y) + x + A
/--
    12 : Binary : ¬(α -> β) : P(x, y) ≡ xy + x (mod 2)
-/
def contraindicating : Dyad -> Dyad -> Dyad :=
    λ x ↦ λ y ↦ (x * y) + x
/--
    13 : Binary : α <- β : P(x, y) ≡ xy + y + 1 (mod 2)
-/
def indicated : Dyad -> Dyad -> Dyad :=
    λ x ↦ λ y ↦ (x * y) + y + A
/--
    14 : Binary : ¬(α <- β) : P(x, y) ≡ xy + y (mod 2)
-/
def contraindicated : Dyad -> Dyad -> Dyad :=
    λ x ↦ λ y ↦ (x * y) + y
/--
    15 : Binary : OR : P(x, y) ≡ xy + x + y (mod 2)
-/
def joined : Dyad -> Dyad -> Dyad :=
    λ x ↦ λ y ↦ (x * y) + x + y
/--
    16 : Binary : NOR : P(x, y) ≡ xy + x + y + 1 (mod 2)
 -/
def unjoined : Dyad -> Dyad -> Dyad :=
    λ x ↦ λ y ↦ (x * y) + x + y + A

/--
    ⊤ ≤ x + ¬x
-/
theorem a_le_a_plus_other_a (x : Dyad) :
    A ≤ x + other x := by
        have h : x + other x = A := by
            cases x <;> aesop
        simp_all only [le_refl]
/--
    ⊤ ≤ x ⊔ ¬x
-/
theorem a_le_a_join_b (x : Dyad) :
    A ≤ joined x (other x) := by
        have h : joined x (other x) = A := by
            cases x <;> aesop
        rw [h]
/--
    x * ¬x ≤ ⊥
-/
theorem b_times_a_le_b (x : Dyad) :
    x * other x ≤ B := by
        have h : x * other x = B := by
            cases x <;> aesop
        simp_all only [le_refl]
/--
    The same two-element algebra.
-/
instance : BooleanAlgebra Dyad where
    sup := λ x y => joined x y
    le_sup_left := λ x y => by
        cases x <;> cases y <;> rfl
    le_sup_right := λ x y => by
        cases x <;> cases y <;> rfl
    sup_le := λ x y z => by
        cases x <;> cases y <;> cases z <;> aesop
    inf := λ x y => x * y
    inf_le_left := λ x y => by
        cases x <;> cases y <;> rfl
    inf_le_right := λ x y => by
        cases x <;> cases y <;> rfl
    le_inf := λ x y z => by
        cases x <;> cases y <;> cases z <;> simp_all [LE.le, LT.lt]
    le_sup_inf := λ x y z => by
        cases x <;> cases y <;> cases z <;> rfl
    compl := λ x => other x
    top := A
    le_top := λ x => by
        cases x <;> rfl
    top_le_sup_compl := a_le_a_join_b
    bot := B
    bot_le := λ x => by
        cases x <;> rfl
    inf_compl_le_bot := b_times_a_le_b
/--
    Mapping from Dyad to Bool.
-/
def dyad_cast : Dyad -> Bool := λ x ↦ match x with
    | A => true
    | B => false
/--
    Mapping from Bool to Dyad.
-/
def cast_dyad : Bool -> Dyad := λ x ↦ match x with
    | true => A
    | false => B
/--
    The mapping between Bool and Dyad is bijective, so
    Dyad is isomorphic to Bool.
-/
def dyad_iso : Dyad ≃ Bool where
    toFun := dyad_cast
    invFun := cast_dyad
    left_inv := λ x ↦ by cases x <;> rfl
    right_inv := λ x ↦ by cases x <;> rfl
/--
    Scalar multiplication by a natural number.
-/
def ns_max_dyad : ℕ -> Dyad -> Dyad := λ n x ↦
    match (n == 0) with
        | true => B
        | false => x
/--
    Scalar multiplication by 0 is always ⊥.
-/
theorem ns_zero_beta (x : Dyad) :
    ns_max_dyad 0 x = B := by
        unfold ns_max_dyad
        simp_all
/--
    Left identity of B.
-/
theorem beta_max (x : Dyad) :
    max B x = x := by
        simp_all only [sup_eq_right]
        simp [LE.le]
        aesop
/--
    Right identity of B.
-/
theorem max_beta (x : Dyad) :
    max x B = x := by
        simp_all only [sup_eq_left]
        simp [LE.le]
        aesop
/--
    x ⊓ A = x
-/
theorem mul_alpha_id (x : Dyad) :
    x * A = x := by
        cases x <;> rfl
/--
    x ⊔ x * B = x
-/
theorem join_id (x : Dyad) :
    max (x * B) x = x := by
        cases x <;> rfl
/--
    x ⊓ B = B
-/
theorem beta_annihilation (x : Dyad) :
    x * B = B := by
        cases x <;> rfl
/--
    B ⊓ x = B
-/
theorem annihilation_beta (x : Dyad) :
    B * x = B := by
        cases x <;> rfl
/--
    Natural scaling rule for Dyads.
-/
theorem ns_dyad_max_law (n : ℕ) (x : Dyad) :
    ns_max_dyad (n + 1) x = max (ns_max_dyad n x) x := by
        have mod_two_cases : n % 2 = 0 ∨ n % 2 = 1 := by
                exact Nat.mod_two_eq_zero_or_one n
        cases mod_two_cases with
            | inl h_zero =>
                simp only [ns_max_dyad]
                simp_all [mul_alpha_id, join_id]
                cases x <;> aesop
            | inr h_one =>
                simp only [ns_max_dyad]
                simp_all [
                    Nat.add_mod,
                    Nat.mod_self,
                    zero_add,
                    beq_self_eq_true,
                    cond_true
                ]
                cases x <;> aesop
/--
    The Boolean semiring on Dyad with max and min (*).
    Establishing an instance of Max/Min
    allows for the use of lemmas which apply to all maximums/minimums.
-/
instance : Semiring Dyad where
    zero := B
    one := A
    add := λ x ↦ λ y ↦ (x * y) + x + y
    zero_add := beta_max -- ↑
    add_zero := max_beta -- ↑
    add_assoc := max_assoc -- Mathlib.Order.Defs.LinearOrder
    add_comm := max_comm -- Mathlib.Order.Defs.LinearOrder
    mul := λ x ↦ λ y ↦ x * y
    one_mul := min_top_left -- Mathlib.Order.BoundedOrder.Lattice
    mul_one := min_top_right -- Mathlib.Order.BoundedOrder.Lattice
    zero_mul := annihilation_beta -- ↑
    mul_zero := beta_annihilation -- ↑
    mul_assoc := min_assoc -- Mathlib.Order.Defs.LinearOrder
    nsmul := ns_max_dyad -- ↑
    nsmul_zero := ns_zero_beta -- ↑
    nsmul_succ := ns_dyad_max_law -- ↑
    left_distrib := min_max_distrib_left -- Mathlib.Order.MinMax
    right_distrib := min_max_distrib_right -- Mathlib.Order.MinMax
/--
    x + x = B
-/
theorem self_cancel (x : Dyad) :
    x + x = B := by
        cases x <;> rfl
/--
    Left distributivity.
-/
theorem times_dist_plus_left (x y z : Dyad) :
    x * (y + z) = (x * y) + (x * z) := by
        cases x <;> cases y <;> cases z <;> rfl -- only feasible with small types.
/--
    Right distributivity.
-/
theorem times_dist_plus_right (x y z : Dyad) :
    (x + y) * z = (x * z) + (y * z) := by
        cases x <;> cases y <;> cases z <;> rfl -- if it ain't broke...
/--
    Natural scaling w/r/t +.
-/
def ns_plus (n : ℕ) (x : Dyad) :=
    match (n % 2 == 1) with
        | true => x
        | false => B
/--
    Under +, each element is its own inverse.
-/
instance : Neg Dyad where
    neg := id
/--
    x² = x
-/
theorem idempotent_square_dyad (x : Dyad) :
    x * x = x := by
        cases x <;> rfl
/-
    The Boolean ring on Dyad with + and *.
-/
instance the_two_ring : BooleanRing Dyad where
    zero := B
    one := A
    neg := id -- + is like XOR, so every element is its own additive inverse.
    add := λ x ↦ λ y ↦ x + y
    zero_add := λ x ↦ by
        cases x <;> rfl
    add_zero := λ x ↦ by
        cases x <;> rfl
    add_assoc := λ x ↦ λ y ↦ λ z ↦ by
        cases x <;> cases y <;> cases z <;> rfl
    add_comm := λ x ↦ λ y ↦ by
        cases x <;> cases y <;> rfl
    neg_add_cancel := self_cancel -- ↑
    mul := λ x ↦ λ y ↦ x * y
    one_mul := min_top_left -- Mathlib.Order.BoundedOrder.Lattice
    mul_one := min_top_right -- Mathlib.Order.BoundedOrder.Lattice
    zero_mul := annihilation_beta -- ↑
    mul_zero := beta_annihilation -- ↑
    mul_assoc := min_assoc -- Mathlib.Order.Defs.LinearOrder
    left_distrib := times_dist_plus_left -- ↑
    right_distrib := times_dist_plus_right -- ↑
    nsmul := nsmulRec -- Mathlib.Algebra.Group.Defs
    natCast := λ n ↦ match (n % 2 == 1) with
        | true => A
        | false => B
    natCast_succ := λ n ↦ by
        have mod_two_cases : n % 2 = 0 ∨ n % 2 = 1 := by
            exact Nat.mod_two_eq_zero_or_one n --  Init.Data.Nat.Lemmas
        cases mod_two_cases with
            | inl h_zero =>
                simp_all
                have h : (n + 1) % 2 == 1 := by
                    simp [h_zero]
                    rw [Nat.add_mod, h_zero] --  Init.Data.Nat.Lemmas
                simp_all [h]
                rfl
            | inr h_one =>
                simp_all
                have h : (n + 1) % 2 == 0 := by
                    simp [h_one]
                    rw [Nat.add_mod, h_one] --  Init.Data.Nat.Lemmas
                simp_all [h]
                rfl
    zsmul := zsmulRec -- Mathlib.Algebra.Group.Defs
    isIdempotentElem := idempotent_square_dyad
/-

    Part 2 : "2ⁿ"

    Set operations take place in a given "universe." We
    cannot have a well-defined notion of "the set of all sets,"
    and so we take a "class" of sets defined by some property,
    and say "this is the universe of sets which we will be working
    with."

    Lean's notion of a universe is similarly a "type of types," but
    type theory can evade the problem of defining a "type of all types"
    no better than set theory can. A type of types must exist at a
    higher "universe level" than the types it contains. Bool is an
    element of Type, which is an element of Type 1, which is an
    element of Type 2, and so on.

    Here, our universe will be some arbitrary set X with finitely
    many elements.

    The "Finset X" for some type X is the set (type) of all finite sets
    of elements of X. If X has finitely many elements, i.e. [Fintype X],
    then Finset X is the set of all subsets of X. Another way of saying this
    is that Finset X is P(X), the power set of X.

    If X has n elements, then Finset X has 2ⁿ elements. The subset
    inclusion relationship, together with ∩ and ∪, forms a
    Boolean lattice on the power set of X.

    Wvery set A ⊆ X has a complement X \ A ⊆ X, where X \ A is the
    set of all elements which are in X but not in A.

    The power set of ∅ is {∅} and forms a trivial Boolean algebra, where
    ∅ is its own complement.

    The power set of {∅} is {∅, {∅}}, and the algebra on ({∅, {∅}}, ∩, ∪)
    is equivalent to the classical propositional logic with
    ({true, false}, ∧, ∨), where logical NOT is absolute complementation.

    Consider that, either obviously or counterintuitively,
    {∅} \ {∅} = ∅, because the set of elements which are in {∅} but
    not in {∅} has no elements in it, and as such is ∅. Similarly,
    {∅} \ ∅ = {∅}, because ∅ ∉ ∅.

    The power set of {∅, {∅}} is {∅, {∅}, {{∅}}, {∅, {∅}}}. Here, it
    already becomes much easier to use letters for arbitrary elements:
    let us say that some set K = {a, b}.

    Then P(K) = {∅, {a}, {b}, {a, b}}. Here, it becomes a lot easier to
    motivate the idea of a partial order. The two-element set has a partial
    order on it, but that partial order happens to also be a total order.
    For Boolean algebras with more than 2 elements in their ground sets,
    the inclusion ordering on their subsets is partial but never total.

    We can already see this in the (four-element) power set of the
    two-element set. {a} ⊆ {a, b}, but {a} ⊈ {b} and {b} ⊈ {a}. Some
    elements can be compared via this relation, but some cannot: the
    ordering is partial but not total.

-/
variable {α : Type*} [DecidableEq α] [Fintype α]
/--
    Set intersection generalizes ∧, in that an element is in
    the intersection of two sets only if it is in *both* of them.
-/
example (s : α) (a b : Finset α) :
    s ∈ a ∩ b ↔ s ∈ a ∧ s ∈ b := by simp
/--
    Set union generalizes ∨, in that an element is in the union
    of two sets if it is in *at least either* of them. That is,
    either or both.
-/
example (s : α) (a b : Finset α) :
    s ∈ a ∪ b ↔ s ∈ a ∨ s ∈ b := by simp
/--
    The difference (or relative complement) of two sets a \ b
    is the set of elements which are in a but *not* in b.
-/
example (s : α) (a b : Finset α) :
    s ∈ a \ b ↔ s ∈ a ∧ s ∉ b := by simp
/--
    The absolute complement of a set a is the set of elements which
    are in that set's universe but not in a.
-/
example (s : α) (a : Finset α) :
    s ∈ (Finset.univ \ a) ↔ ¬(s ∈ a) := by simp
/--
    Symmetric difference generalizes ⊕. The *symmetric* difference
    of two sets a ∆ b is the set of
    elements which are in *exactly either* of them. That is,
    either but *not* both.
-/
example (s : α) (a b : Finset α) :
    s ∈ (symmDiff a b) ↔ (s ∈ a) ^^ (s ∈ b) := by
        rw [Finset.mem_symmDiff]
        simp_all
        tauto
/--
    Union distributes over intersection for subsets.
-/
theorem union_inter_dist (a b c : Finset α) :
    (a ∪ b) ∩ (a ∪ c) ⊆ a ∪ b ∩ c := by
        rw [<- Finset.union_inter_distrib_left]
/--
    Union distributes over intersection.
-/
theorem union_inter_dist_eq (a b c : Finset α) :
    (a ∪ b) ∩ (a ∪ c) = a ∪ b ∩ c := by
        rw [<- Finset.union_inter_distrib_left]
/--
    The union of the intersection of a and b and the set difference
    of a and b is a.
-/
theorem complement_sup_inf (a b : Finset α) :
    (a ∩ b) ∪ (a \ b) = a := by
        rw [Finset.union_comm, Finset.sdiff_union_inter]
/--
    The intersection of the intersection of a and b and the
    set difference of a and b is the empty set.
-/
theorem complement_inf_inf (a b : Finset α) :
    (a ∩ b) ∩ (a \ b) = ∅ := by
        let c := a ∩ b;
        have h1 : a \ b = a \ c := by
            rw [Finset.sdiff_inter_self_left]
        rw [h1]
        change c ∩ (a \ c) = ∅
        apply Finset.inter_sdiff_self
/--
    The universe set is a subset of the union of a and
    the absolute complement of a.
-/
theorem univ_union_incl_univ (a : Finset α) :
    Finset.univ ⊆ a ∪ (Finset.univ \ a) := by
        rw [Finset.union_comm]
        rw [Finset.sdiff_union_of_subset]
        apply Finset.subset_univ
/--
    The intersection of a and its absolute complement is
    a subset of the empty set. Note that the only subset of
    the empty set is the empty set.
-/
theorem univ_inter_empty (a : Finset α) :
    a ∩ (Finset.univ \ a) ⊆ ∅ := by
        rw [Finset.inter_sdiff_self]
/--
    The intersection of a and its absolute complement is the empty set.
-/
theorem self_inter_compl_empty (a : Finset α) :
     a ∩ (Finset.univ \ a) = ∅ := by simp
/--
    The intersection of a and b is a subset of the union of a and b.
-/
theorem inter_subs_union (a b : Finset α) :
    a ∩ b ⊆ a ∪ b := by
        intro x hx
        simp only [Finset.mem_union] at *
        left
        exact Finset.mem_of_mem_inter_left hx
/--
    The intersection of a and the absolute complement of b is
    the set difference of a and the intersection of a and b.
-/
theorem inter_compl (a b  : Finset α) :
    a ∩ (Finset.univ \ b) = a \ (a ∩ b) := by
        rw [Finset.sdiff_inter_self_left]
        ext a_1 : 1 -- "apply extensionality"
        simp_all only [
            Finset.mem_inter,
            Finset.mem_sdiff,
            Finset.mem_univ,
            true_and
        ]
/--
    Generalized logical implication: x is an element of the union
    of b and the absolute complement of a if and only if x is not in a
    or x is in b.
-/
theorem mem_imp {a b : Finset α} {x : α} :
    x ∈ b ∪ (Finset.univ \ a) ↔ x ∉ a ∨ x ∈ b := by
        simp [or_comm]
/--
    The finite subsets of a finite set form a Boolean lattice,
    where the subset relation is a weak partial order:

    ∀ a, b, c ∈ P(α),

    1. a ⊆ a
    2. a ⊆ b ∧ b ⊆ a -> a = b
    3. a ⊆ b ∧ b ⊆ c -> a ⊆ c

    Every pair of elements a, b ∈ P(α) has a unique supremum
    or "join," which is set union ∪.

    a ⊆ a ∪ b ∧ b ⊆ a ∪ b.

    a ∪ b is the least upper bound on a and b.

    Every pair of elements a, b ∈ P(α) has a unique infimum
    or "meet," which is set intersection ∩.

    a ∩ b ⊆ a ∧ a ∩ b ⊆ b

    a ∩ b is the greatest lower bound on a and b.

    Union distributes over intersection.

    There is an absolute complement.

    There is a maximal element, which is the universe set.

    Within a universe, every set is a subset of the universe.

    For any set a in the universe, the universe is a subset of
    the union of a and its absolute complement.

    There is a minimal element, which is the empty set ∅.

    The empty subset is a subset of every set.

    The intersection of any set a in the universe and the
    absolute complement of a is ∅.

-/
instance power_set_algebra : BooleanAlgebra (Finset α) where
    le := λ a b ↦ a ⊆ b
    le_refl := λ a ↦ subset_refl a
    le_trans := λ _ _ _ ↦ subset_trans
    le_antisymm := λ _ _ ↦ subset_antisymm
    sup := λ a b ↦ a ∪ b
    le_sup_left := λ _ _ ↦ Finset.subset_union_left
    le_sup_right := λ _ _ ↦ Finset.subset_union_right
    sup_le := λ _ _ _ ↦ Finset.union_subset
    inf := λ a b ↦ a ∩ b
    inf_le_left := λ _ _ ↦ Finset.inter_subset_left
    inf_le_right := λ _ _ ↦ Finset.inter_subset_right
    le_inf := λ _ _ _ ↦ Finset.subset_inter
    le_sup_inf := union_inter_dist
    compl := λ a ↦ Finset.univ \ a
    top := Finset.univ
    le_top := Finset.subset_univ
    top_le_sup_compl := univ_union_incl_univ
    bot := ∅
    bot_le := Finset.empty_subset
    inf_compl_le_bot := univ_inter_empty
/-
    The lattice of a power set of a set with n elements is
    modeled by the vertices of a hypercube in n dimensions
    (or "n-cube"). That is to say that an n-cube has 2ⁿ vertices.

    A 0-cube is a point, and as such has
    1 vertex.

    ( )

    A 1-cube is a line segment, and as such
    has 2 vertices.

    ( )---------------(a)

    A 2-cube is a square.

    ( )----------------(b)
     |                  |
     |                  |
     |                  |
     |                  |
     |                  |
     |                  |
    (a)----------------(a, b)

    A 3-cube is a...cube.

    ( )----------------(b)
     | \                | \
     |  \               |  \
     |   \              |   \
     |    \             |    \
     |     (c)----------------(b, c)
     |      |           |      |
    (a)-----|----------(a, b)  |
       \    |             \    |
        \   |              \   |
         \  |               \  |
          \ |                \ |
       (a, c)-------------(a, b, c)
-/
/-
    As with the two-element algebra, where forming a
    Boolean lattice with ∨ and ∧ means that
    (∨, ∧, false, true) forms a semiring, the
    more general power set algebra forming a Boolean
    lattice with ∪ and ∩ means that, for some finite
    universe X, (∪, ∩, ∅, X) forms a semiring.
-/
def ns_union (n : ℕ) (a : Finset α) :=
    match n with
        | 0 => ∅
        | _ => a
/--
    Since the union-intersection semiring is another "classic"
    mathematical object, the relevant lemmas are largely all
    available on Mathlib.
    One can often wing it by "thinking algebraically" with Lean's
    naming conventions. For example, I was not exactly sure
    there would be a "Finset.inter_univ" lemma, but since the
    proof requirement is "mul_one," "mul" is intersection,
    and "one" is the universe set, it is sensible to replace
    them for their abbreviations and pray that some industrious
    mathematician has already written the proof for the property
    and given it a sensible name.
-/
instance : Semiring (Finset α) where
    zero := ∅
    one := Finset.univ
    add := λ a ↦ λ b ↦ a ∪ b
    add_assoc := Finset.union_assoc
    zero_add := Finset.empty_union
    add_zero := Finset.union_empty
    add_comm := Finset.union_comm
    mul := λ a ↦ λ b ↦ a ∩ b
    mul_assoc := Finset.inter_assoc
    zero_mul := Finset.empty_inter
    mul_zero := Finset.inter_empty
    one_mul := Finset.univ_inter
    mul_one := Finset.inter_univ
    left_distrib := λ a ↦ λ b ↦ λ c ↦ by
        change a ∩ (b ∪ c) = a ∩ b ∪ a ∩ c
        aesop
    right_distrib := Finset.union_inter_distrib_right
    nsmul := ns_union
    nsmul_succ := by
        intro n
        induction n with
            | zero =>
                unfold ns_union
                intro x
                simp_all
                change x = ∅ ∪ x
                simp [Finset.empty_union]
            | succ k ih =>
                unfold ns_union
                simp_all
                change ∀ (x : Finset α), x = x ∪ x
                simp_all
/--
    The natural way to "scale" symmetric difference for
    natural numbers.
-/
def ns_symm (n : ℕ) (a : Finset α) :=
    match n % 2 with
        | 0 => ∅
        | _ => a
/--
    The natural way to "scale" symmetric differnce for integers.
    Effectively the same function as "ns_symm," but takes
    integers, then explicitly casts them to natural numbers.
-/
def zs_symm (n : ℤ) (a : Finset α) :=
    let k : ℕ := n.natAbs
    if (k % 2 == 0) then ∅ else a
/--
    ∅ is the "additive identity" for symmetric difference.
-/
theorem symm_diff_empty (a : Finset α) :
    symmDiff ∅ a = a := by simp
/--
    A set is its own "additive inverse" under symmetric difference.
-/
theorem symm_diff_cancel_self (a : Finset α) :
    symmDiff a a = ∅ := by simp -- symmDiff_self, Mathlib.Order.SymmDiff
/--
    If the symmetric difference of a set and itself "scaled" by n is that same
    set, then that set scaled by n + 1 will be the empty set.
-/
@[simp]
theorem ns_full_succ_empty (n : ℕ) (a : Finset α):
    ns_symm n a = a → ns_symm (n + 1) a = ∅ := by
        have mod_two_cases : n % 2 = 0 ∨ n % 2 = 1 := by
            exact Nat.mod_two_eq_zero_or_one n
        intro h
        unfold ns_symm at *
        cases mod_two_cases with
            | inl h_zero =>
                simp_all [h]
                cases a; aesop
            | inr h_one =>
                simp_all [h, h_one]
                rw [Nat.add_mod, h_one]
/--
    Verifies that symmetric difference "scaled" by a natural number
    "works as expected," as it were.
-/
theorem ns_symm_succ (n : ℕ) (a: Finset α) :
    ns_symm (n + 1) a = symmDiff (ns_symm n a) a := by
        have mod_two_cases : n % 2 = 0 ∨ n % 2 = 1 := by
            exact Nat.mod_two_eq_zero_or_one n
        cases mod_two_cases with
            | inl h_zero =>
                simp only [ns_symm]
                rw [h_zero]
                simp only [beq_self_eq_true, cond_true]
                rw [Nat.add_mod, h_zero]
                have h : a = symmDiff ∅ a := by
                    change a = symmDiff ⊥ a
                    rw [bot_symmDiff]
                rw [h]
                simp [h_zero]
            | inr h_one =>
                simp only [ns_symm]
                rw [h_one]
                simp only [beq_self_eq_true, cond_true]
                rw [Nat.add_mod, h_one]
                have h : a = symmDiff ∅ a := by
                    change a = symmDiff ⊥ a
                    rw [bot_symmDiff]
                rw [h]
                simp [h_one]
/--
    Map from ℕ to the ring of subsets of a finite set X
    with (∆, ∩, ∅, X).
-/
def natural_cast : ℕ -> (Finset α) :=
    λ n ↦ match (n % 2 == 1) with
        | true => Finset.univ
        | _ => ∅
/--
    Also analogous to the two-element algebra, where
    (⊕, ∧, false, true) forms a Boolean ring, the power
    set of a finite set X forms a Boolean ring with
    (∆, ∩, ∅, X).
-/
instance : BooleanRing (Finset α) where
    zero := ∅
    one := Finset.univ
    neg := id
    add := λ a ↦ λ b ↦ symmDiff a b
    add_assoc := symmDiff_assoc
    zero_add := λ a ↦ by
        change symmDiff ∅ a = a
        simp
    add_zero := λ a ↦ by
        change symmDiff a ∅ = a
        simp
    add_comm := symmDiff_comm
    mul := λ a ↦ λ b ↦ a ∩ b
    mul_assoc := Finset.inter_assoc
    zero_mul := Finset.empty_inter
    mul_zero := Finset.inter_empty
    one_mul := Finset.univ_inter
    mul_one := Finset.inter_univ
    left_distrib := inf_symmDiff_distrib_left
    right_distrib := inf_symmDiff_distrib_right
    neg_add_cancel := symm_diff_cancel_self
    nsmul := ns_symm
    nsmul_succ := ns_symm_succ
    zsmul := zs_symm
    isIdempotentElem := Finset.inter_self
    natCast := natural_cast
    natCast_succ := λ n ↦ by
        change natural_cast (n + 1) = symmDiff (natural_cast n) Finset.univ
        unfold natural_cast
        have mod_two_cases : n % 2 = 0 ∨ n % 2 = 1 := by
            exact Nat.mod_two_eq_zero_or_one n
        cases mod_two_cases with
        | inl h_zero =>
            rw [h_zero]
            --simp only [beq_iff_eq, cond_false]
            rw [Nat.add_mod, h_zero]
            simp only [beq_self_eq_true, cond_true]
            simp_all only [Nat.reduceBEq]
            rw [symm_diff_empty]
        | inr h_one =>
            rw [h_one]
            simp only [beq_self_eq_true, cond_true]
            rw [Nat.add_mod, h_one]
            rw [symm_diff_cancel_self]
            aesop
    zsmul_succ' := by
        intro n a
        simp_all [
            Nat.succ_eq_add_one,
            Nat.cast_add,
            Nat.cast_one,
            Nat.add_mod
        ]
        simp_all [zs_symm]
        change (if (n + 1) % 2 = 0 then ∅ else a) = symmDiff (if n % 2 = 0 then ∅ else a) a
        have mod_two_cases : n % 2 = 0 ∨ n % 2 = 1 := by
            exact Nat.mod_two_eq_zero_or_one n
        cases mod_two_cases with
            | inl h_zero =>
                rw [h_zero]
                have h' : n % 2 = 0 → (n + 1) % 2 = 1 := by
                    simp_all [
                        Nat.mod_two_eq_zero_or_one
                    ]
                    rw [Nat.add_mod]
                    simp_all
                rw [h']
                simp_all only [forall_const, one_ne_zero, ↓reduceIte]
                rw [symm_diff_empty]
                exact h_zero
            | inr h_one =>
                rw [h_one]
                have h' : n % 2 = 1 → (n + 1) % 2 = 0 := by
                    simp_all [
                        Nat.mod_two_eq_zero_or_one
                    ]
                    rw [Nat.add_mod]
                    simp_all
                rw [h']
                simp_all only [forall_const, one_ne_zero, ↓reduceIte]
                rw [symm_diff_cancel_self]
                exact h_one
