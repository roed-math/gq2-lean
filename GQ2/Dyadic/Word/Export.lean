/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
module

public import GQ2.Dyadic.Word.Syntax

@[expose] public section

/-!
# Dyadic campaign, ticket WW5: the one-tree export layer

Merge gate 7 (plan §7) asks that the branch words' TeX and Lean be generated from **one**
expression tree, with that tree's content hash emitted into both and compared
mechanically.  This file is the Lean half; `scripts/dyadic_word_tex.py` is the TeX half
and the comparison (which `scripts/check_dyadic.sh`'s D4 hook calls).

## The one tree

`RawWord` below is the *simplification* campaign's word AST, mirrored constructor for
constructor — deliberately the same names, arities and field order that
`dyadic_search/words/pretty_lean.py` already emits into `generated/lean/<Name>.lean`
(ticket S5.G).  A generated term therefore elaborates against this type **verbatim**:
that is the point, and it is why this file does not invent a second Lean encoding.

`RawWord` is *data*.  It carries no proofs and is never itself the subject of a group
theorem; `denote` (below) is the bridge to F2's `PWord`, and it is `PWord` that the Fox,
Stokes and Hessian lanes evaluate.

## The hash rule of the house

One definition of a word's identity, the simplification campaign's
(`dyadic_search/words/ast.py`, ticket S1.1):

* `canonicalJson w` is `json.dumps(to_json(w), sort_keys=True, separators=(",", ":"),
  ensure_ascii=True)` — reproduced here byte for byte, keys emitted in sorted order,
  no whitespace, non-ASCII escaped;
* `astHash w` is the SHA-256 hex digest of those bytes, UTF-8 encoded.

`AST_SCHEMA_VERSION` travels in the certificate envelope and is deliberately **not**
hashed.  `canon` performs the one constructor-level normalization the Python
dataclasses perform (`EtaHat` → positive denominator, gcd-reduced; ticket S1.M), reusing
F2's already-proved `canonicalEtaHat`, so a Lean-authored spelling of an exponent cannot
change a word's identity either.

Checking is two-tier, and both tiers are axiom-clean:

* the tree → bytes step is pinned in the **kernel** (`canonicalJson w = "…"` by `rfl`);
* the bytes → digest step is checked by `#eval` (`assertAstHash`), which runs at
  elaboration time and fails the build on mismatch.  `native_decide` is deliberately
  *not* used anywhere here: it would add `Lean.ofReduceBool` to the axiom census, and
  this file must print `std-3`.

## What `PWord` has that the Python AST does not, and conversely

`RawWord` is the interchange vocabulary; `PWord` is the semantic one.  They are not
isomorphic, and the differences are the wave-2 gate list:

Four `RawWord` nodes have **no `PWord` constructor** and are therefore *derived syntax*
on the Lean side; `denote` is where each is discharged.

* `orbitNorm U m z` — **expanded** to `z^{U^1} ⋯ z^{U^m}`, which needs a concrete `m`.
  The group-level block is `GQ2.Dyadic.orbitNorm` (S1.9, `Blocks.lean`).
* `hyperbolicHandles s h` — **expanded** to `[x_s,x_{s+1}] ⋯`, over the generators
  `DenoteCtx.handleGen` supplies; group-level block `handlesProd`.
* `auxiliary n d` — **inlined** to `d`; the name is display and complexity bookkeeping.
* `shadow k p w` — **`none`**: no denotation exists.  Its semantics are owned by
  simplification ticket S4.2, and inventing one here is what the ledger forbids.

One further node is only partial: `integerPower w e` with a *symbolic* `e`, because
`PWord.zpow` takes a plain `ℤ`.  `denote` evaluates it through `DenoteCtx.param` and
returns `none` on an unassigned parameter.

The gap in the other direction is `PWord.z2pow w z` (`ℤ₂`-powers, packet Rem. 2.3): the
frozen S1.1 grammar has **no** `ℤ₂`-power node, so a word using `z2pow` has no
interchange form and cannot be hashed at all.

The four expanded/inlined nodes are the sense in which those nodes are *derived syntax*
on the Lean side.  **The hash is always of the unexpanded tree**: `astHash` never
expands a block, so the TeX and the Lean name the same tree, and expansion is a
downstream definitional step that happens inside `denote` only.  Were the hash taken
after expansion the two sides would disagree the moment a block appeared, which is
exactly the failure merge gate 7 exists to catch.

The `z2pow` gap is the only *irreducible* one, and closing it needs a new node in the
frozen Python grammar — an orchestrator-approved S1.1 migration note, not a change here.

## Implementation notes

`module`-style, and its single in-repo import (`GQ2.Dyadic.Word.Syntax`) is
`module`-style too, so plan §3 A5's one-directional rule holds.  Nothing here is imported
by `GQ2.lean`: this file is tooling for the gate, and no proof cites it.
-/

namespace GQ2.Dyadic.Export

/-! ## SHA-256

A self-contained SHA-256 (FIPS 180-4).  It exists so that the Lean side can hash *its
own* tree rather than trust a string literal: without it the gate would only compare the
TeX against a constant nobody checked, and a word could be edited without its hash
moving.  Used through `#eval` (`assertAstHash`), never through `native_decide`.
-/

namespace Sha256

/-- The 64 round constants (FIPS 180-4 §4.2.2). -/
def roundConstants : Array UInt32 :=
  #[0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1,
    0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
    0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147,
    0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
    0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
    0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The initial hash value (FIPS 180-4 §5.3.3). -/
def initialState : Array UInt32 :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- Rotate right, for `0 < n < 32`. -/
def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

def bsig0 (x : UInt32) : UInt32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
def bsig1 (x : UInt32) : UInt32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
def ssig0 (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
def ssig1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)
def ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ ((x ^^^ 0xffffffff) &&& z)
def maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- Append `n` zero bytes. -/
def pushZeros (b : ByteArray) : Nat → ByteArray
  | 0 => b
  | n + 1 => pushZeros (b.push 0) n

/-- The FIPS 180-4 §5.1.1 padding: `0x80`, zeros to 56 mod 64, then the big-endian
64-bit message length in **bits**. -/
def pad (bs : ByteArray) : ByteArray := Id.run do
  let len := bs.size
  let zeros := (56 + 64 - (len + 1) % 64) % 64
  let mut out := pushZeros (bs.push 0x80) zeros
  let bits : UInt64 := (len.toUInt64) * 8
  for i in [0:8] do
    out := out.push ((bits >>> ((7 - i) * 8).toUInt64).toUInt8)
  return out

/-- The big-endian 32-bit word at byte offset `i`. -/
def word32BE (b : ByteArray) (i : Nat) : UInt32 :=
  (b[i]!.toUInt32 <<< 24) ||| (b[i + 1]!.toUInt32 <<< 16)
    ||| (b[i + 2]!.toUInt32 <<< 8) ||| b[i + 3]!.toUInt32

/-- The 64-word message schedule of the block at byte offset `off`. -/
def schedule (b : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := #[]
  for i in [0:16] do
    w := w.push (word32BE b (off + 4 * i))
  for i in [16:64] do
    w := w.push (ssig1 w[i - 2]! + w[i - 7]! + ssig0 w[i - 15]! + w[i - 16]!)
  return w

/-- One block of the compression function (FIPS 180-4 §6.2.2). -/
def compress (st : Array UInt32) (w : Array UInt32) : Array UInt32 := Id.run do
  let mut a := st[0]!; let mut b := st[1]!; let mut c := st[2]!; let mut d := st[3]!
  let mut e := st[4]!; let mut f := st[5]!; let mut g := st[6]!; let mut h := st[7]!
  for i in [0:64] do
    let t1 := h + bsig1 e + ch e f g + roundConstants[i]! + w[i]!
    let t2 := bsig0 a + maj a b c
    h := g; g := f; f := e; e := d + t1
    d := c; c := b; b := a; a := t1 + t2
  return #[st[0]! + a, st[1]! + b, st[2]! + c, st[3]! + d,
           st[4]! + e, st[5]! + f, st[6]! + g, st[7]! + h]

/-- A lowercase hex digit. -/
def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Eight lowercase hex digits, big-endian. -/
def hex8 (x : UInt32) : String :=
  let n := x.toNat
  String.ofList ((List.range 8).map fun i => hexDigit (n / (16 ^ (7 - i)) % 16))

/-- The SHA-256 hex digest of a byte array. -/
def digest (bs : ByteArray) : String := Id.run do
  let padded := pad bs
  let mut st := initialState
  for blk in [0 : padded.size / 64] do
    st := compress st (schedule padded (blk * 64))
  return String.join (st.toList.map hex8)

/-- The SHA-256 hex digest of a string's UTF-8 encoding — what `content_hash` digests. -/
def hex (s : String) : String := digest s.toUTF8

end Sha256

/-! ## The mirrored word syntax

Constructor names, arities and field names are `pretty_lean.py`'s `_PRELUDE` verbatim, so
a `generated/lean/<Name>.lean` term elaborates against these declarations unchanged.
-/

/-- Symbolic integer-exponent expressions (S1.1: `Int | Param | Add | Sub | Mul | Pow2`).
Concrete backends evaluate these to integers before use. -/
inductive RawExp where
  /-- An integer literal. -/
  | int (n : Int)
  /-- A named integer parameter (`alpha`, `r`, `m`, …). -/
  | param (name : String)
  /-- Sum. -/
  | add (l r : RawExp)
  /-- Difference. -/
  | sub (l r : RawExp)
  /-- Product. -/
  | mul (l r : RawExp)
  /-- `2 ^ e`. -/
  | pow2 (e : RawExp)
  deriving DecidableEq, Repr, Inhabited

/-- Finite (profinite) exponent specs — the pinned S1.1/S1.2 contract, wire forms
`("int", n) / ("omega2",) / ("etahat", num, den)`.  `etahat num den` has odd `num`, `den`
and denotes the exponent whose `2`-component is `num · den⁻¹` and whose odd-primary
components are all `1`, i.e. F2's `etaHatZ`. -/
inductive RawSpec where
  /-- An integer exponent, read in `ℤ̂`. -/
  | int (n : Int)
  /-- The idempotent `ω₂`. -/
  | omega2
  /-- `η̂` for `η = num · den⁻¹`. -/
  | etahat (num den : Int)
  deriving DecidableEq, Repr, Inhabited

/-- A `Shadow` parameter value: a string tag or an exponent expression. -/
inductive RawParam where
  /-- A string tag. -/
  | str (s : String)
  /-- An exponent expression. -/
  | exp (e : RawExp)
  deriving DecidableEq, Repr, Inhabited

/-- The campaign word syntax, mirroring `dyadic_search/words/ast.py` constructor for
constructor.  This is **data**: it carries no proofs, and `denote` is its bridge to
`PWord`. -/
inductive RawWord where
  /-- A named topological generator. -/
  | generator (name : String)
  /-- The empty word. -/
  | identity
  /-- An ordered product, in displayed order. -/
  | multiply (factors : List RawWord)
  /-- `w⁻¹`. -/
  | inverse (w : RawWord)
  /-- `w ^ e` for an integer (possibly symbolic) exponent. -/
  | integerPower (w : RawWord) (e : RawExp)
  /-- `w ^ s` for a profinite exponent spec. -/
  | zhatPower (w : RawWord) (s : RawSpec)
  /-- `w ^ ω₂`. -/
  | omega2Power (w : RawWord)
  /-- `w ^ g = g⁻¹ w g`. -/
  | conjugate (w g : RawWord)
  /-- `[l, r] = l⁻¹ r⁻¹ l r`. -/
  | commutator (l r : RawWord)
  /-- `𝒩_{step, length}(w) = ∏_{j=1}^{length} w^{step^j}`. -/
  | orbitNorm (step : RawWord) (length : RawExp) (w : RawWord)
  /-- A restricted shadow block; semantics owned by simplification ticket S4.2. -/
  | shadow (kind : String) (parameters : List (String × RawParam)) (w : RawWord)
  /-- `∏_{j=0}^{count-1} [x_{startIndex+2j}, x_{startIndex+1+2j}]`. -/
  | hyperbolicHandles (startIndex : Nat) (count : RawExp)
  /-- A named auxiliary definition; display and complexity bookkeeping only. -/
  | auxiliary (name : String) (defn : RawWord)
  deriving Repr, Inhabited

/-! ## Canonicalization

Exactly the normalization the Python dataclass *constructors* perform, and nothing else:
no factor is reordered, no power folded, no block expanded.  Whatever normal form a
caller wants travels in the tree.
-/

/-- The S1.M canonicalization of a finite exponent spec, delegated to F2's
`canonicalEtaHat` (positive denominator, gcd-reduced) — so the Lean and Python
representatives of one `2`-adic unit agree, and hence so do their hashes. -/
def RawSpec.canon : RawSpec → RawSpec
  | .etahat num den =>
      let e := canonicalEtaHat ⟨num, den⟩
      .etahat e.num e.den
  | s => s

mutual

/-- Constructor-level canonicalization of a whole tree. -/
def RawWord.canon : RawWord → RawWord
  | .generator n => .generator n
  | .identity => .identity
  | .multiply fs => .multiply (RawWord.canonList fs)
  | .inverse w => .inverse w.canon
  | .integerPower w e => .integerPower w.canon e
  | .zhatPower w s => .zhatPower w.canon s.canon
  | .omega2Power w => .omega2Power w.canon
  | .conjugate w g => .conjugate w.canon g.canon
  | .commutator l r => .commutator l.canon r.canon
  | .orbitNorm u m z => .orbitNorm u.canon m z.canon
  | .shadow k ps w => .shadow k ps w.canon
  | .hyperbolicHandles s c => .hyperbolicHandles s c
  | .auxiliary n d => .auxiliary n d.canon

/-- `RawWord.canon`, factorwise. -/
def RawWord.canonList : List RawWord → List RawWord
  | [] => []
  | w :: ws => w.canon :: RawWord.canonList ws

end

/-! ## Well-formedness

`Bool`-valued and therefore `decide`-friendly.  These are the side conditions the Python
constructors raise on; a tree failing them has no Python counterpart, so its hash would
be meaningless rather than merely different.
-/

/-- Odd numerator and denominator, as `EtaHat.__post_init__` requires. -/
def RawSpec.wf : RawSpec → Bool
  | .etahat num den => num % 2 != 0 && den % 2 != 0
  | _ => true

/-- Shadow parameter keys: nonempty, and strictly increasing.

Python *sorts* the pairs in the constructor; canonicalizing here would need a string
sort, so instead this is a checked precondition — a generated tree is already sorted, and
a hand-written unsorted one fails loudly rather than hashing to something Python would
never produce. -/
def paramsWf : List (String × RawParam) → Bool
  | [] => true
  | [p] => !p.1.isEmpty
  | p :: q :: rest => !p.1.isEmpty && decide (p.1 < q.1) && paramsWf (q :: rest)

mutual

/-- Every name nonempty, every `etahat` odd, every shadow parameter list sorted. -/
def RawWord.wf : RawWord → Bool
  | .generator n => !n.isEmpty
  | .identity => true
  | .multiply fs => RawWord.wfList fs
  | .inverse w => w.wf
  | .integerPower w _ => w.wf
  | .zhatPower w s => w.wf && s.wf
  | .omega2Power w => w.wf
  | .conjugate w g => w.wf && g.wf
  | .commutator l r => l.wf && r.wf
  | .orbitNorm u _ z => u.wf && z.wf
  | .shadow k ps w => !k.isEmpty && paramsWf ps && w.wf
  | .hyperbolicHandles _ _ => true
  | .auxiliary n d => !n.isEmpty && d.wf

/-- `RawWord.wf`, factorwise. -/
def RawWord.wfList : List RawWord → Bool
  | [] => true
  | w :: ws => w.wf && RawWord.wfList ws

end

/-! ## Canonical JSON

`json.dumps(to_json(w), sort_keys=True, separators=(",", ":"), ensure_ascii=True)`,
reproduced byte for byte: fields are emitted in **sorted key order** (which is why, say,
`Conjugate` prints `conjugator` before `op` before `word`), there is no whitespace, and
strings are escaped the way CPython's `ensure_ascii` encoder escapes them.
-/

/-- A digit character, by literal table.  `Char.ofNat` goes through a validity check
that the kernel will not unfold, and every declaration in this section has to reduce for
the `rfl` pins below to be kernel work. -/
def digitChar : Nat → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4' | 5 => '5' | 6 => '6'
  | 7 => '7' | 8 => '8' | 9 => '9' | 10 => 'a' | 11 => 'b' | 12 => 'c' | 13 => 'd'
  | 14 => 'e' | _ => 'f'

/-- Decimal digits of `n`, most significant first, on a fuel argument so that the
recursion is structural. -/
def decimalDigits : Nat → Nat → List Char
  | 0, _ => []
  | _ + 1, 0 => []
  | fuel + 1, n => decimalDigits fuel (n / 10) ++ [digitChar (n % 10)]

/-- `Nat` in decimal.  Not `toString`: `Nat.repr` does not reduce in the kernel, and the
byte-level pins below are `rfl`. -/
def natToString (n : Nat) : String :=
  if n == 0 then "0" else String.ofList (decimalDigits (n + 1) n)

/-- `Int` in decimal, with CPython's spelling of a negative (`-3`, no space). -/
def intToString (n : Int) : String :=
  if n < 0 then "-" ++ natToString n.natAbs else natToString n.natAbs

/-- Four lowercase hex digits — a `\uXXXX` payload. -/
def hex4 (n : Nat) : String :=
  String.ofList [digitChar (n / 4096 % 16), digitChar (n / 256 % 16),
             digitChar (n / 16 % 16), digitChar (n % 16)]

/-- One character, CPython-escaped. -/
def escapeChar (c : Char) : String :=
  let n := c.toNat
  if c == '"' then "\\\""
  else if c == '\\' then "\\\\"
  else if n == 8 then "\\b"
  else if n == 9 then "\\t"
  else if n == 10 then "\\n"
  else if n == 12 then "\\f"
  else if n == 13 then "\\r"
  else if n < 0x20 || n > 0x7e then
    if n < 0x10000 then "\\u" ++ hex4 n
    else "\\u" ++ hex4 (0xd800 + (n - 0x10000) / 0x400)
           ++ "\\u" ++ hex4 (0xdc00 + (n - 0x10000) % 0x400)
  else String.singleton c

/-- `escapeChar`, characterwise.  Structural recursion on `List Char` rather than
`String.foldl`, because `String.foldl` goes through `String.Iterator` and does **not**
reduce in the kernel — and the byte-level pins below are `rfl`, i.e. kernel work. -/
def escapeChars : List Char → String
  | [] => ""
  | c :: cs => escapeChar c ++ escapeChars cs

/-- CPython's `json.dumps(..., ensure_ascii=True)` string encoding, quotes included:
`"` and `\` backslash-escaped, the five short escapes for `\b \t \n \f \r`, every other
character outside printable ASCII as `\uXXXX` (a surrogate pair beyond the BMP). -/
def jsonString (s : String) : String := "\"" ++ escapeChars s.toList ++ "\""

/-- Canonical JSON of an exponent expression. -/
def RawExp.toJson : RawExp → String
  | .int n => "{\"type\":\"Int\",\"value\":" ++ intToString n ++ "}"
  | .param name => "{\"name\":" ++ jsonString name ++ ",\"type\":\"Param\"}"
  | .add l r => "{\"left\":" ++ l.toJson ++ ",\"right\":" ++ r.toJson ++ ",\"type\":\"Add\"}"
  | .sub l r => "{\"left\":" ++ l.toJson ++ ",\"right\":" ++ r.toJson ++ ",\"type\":\"Sub\"}"
  | .mul l r => "{\"left\":" ++ l.toJson ++ ",\"right\":" ++ r.toJson ++ ",\"type\":\"Mul\"}"
  | .pow2 e => "{\"exponent\":" ++ e.toJson ++ ",\"type\":\"Pow2\"}"

/-- Canonical JSON of a finite exponent spec. -/
def RawSpec.toJson : RawSpec → String
  | .int n => "{\"type\":\"Int\",\"value\":" ++ intToString n ++ "}"
  | .omega2 => "{\"type\":\"Omega2\"}"
  | .etahat num den =>
      "{\"den\":" ++ intToString den ++ ",\"num\":" ++ intToString num
        ++ ",\"type\":\"EtaHat\"}"

/-- Canonical JSON of a shadow parameter value. -/
def RawParam.toJson : RawParam → String
  | .str s => jsonString s
  | .exp e => e.toJson

/-- Canonical JSON of a shadow parameter list: `[[key, value], …]`. -/
def paramsToJson : List (String × RawParam) → String
  | [] => ""
  | [p] => "[" ++ jsonString p.1 ++ "," ++ p.2.toJson ++ "]"
  | p :: ps => "[" ++ jsonString p.1 ++ "," ++ p.2.toJson ++ "]," ++ paramsToJson ps

mutual

/-- Canonical JSON of a word node — the exact byte string `astHash` digests. -/
def RawWord.toJson : RawWord → String
  | .generator name => "{\"name\":" ++ jsonString name ++ ",\"op\":\"Generator\"}"
  | .identity => "{\"op\":\"Identity\"}"
  | .multiply fs => "{\"children\":[" ++ RawWord.listToJson fs ++ "],\"op\":\"Multiply\"}"
  | .inverse w => "{\"op\":\"Inverse\",\"word\":" ++ w.toJson ++ "}"
  | .integerPower w e =>
      "{\"exponent\":" ++ e.toJson ++ ",\"op\":\"IntegerPower\",\"word\":" ++ w.toJson ++ "}"
  | .zhatPower w s =>
      "{\"exponent_spec\":" ++ s.toJson ++ ",\"op\":\"ZhatPower\",\"word\":" ++ w.toJson ++ "}"
  | .omega2Power w => "{\"op\":\"Omega2Power\",\"word\":" ++ w.toJson ++ "}"
  | .conjugate w g =>
      "{\"conjugator\":" ++ g.toJson ++ ",\"op\":\"Conjugate\",\"word\":" ++ w.toJson ++ "}"
  | .commutator l r =>
      "{\"left\":" ++ l.toJson ++ ",\"op\":\"Commutator\",\"right\":" ++ r.toJson ++ "}"
  | .orbitNorm u m z =>
      "{\"length\":" ++ m.toJson ++ ",\"op\":\"OrbitNorm\",\"step\":" ++ u.toJson
        ++ ",\"word\":" ++ z.toJson ++ "}"
  | .shadow k ps w =>
      "{\"kind\":" ++ jsonString k ++ ",\"op\":\"Shadow\",\"parameters\":["
        ++ paramsToJson ps ++ "],\"word\":" ++ w.toJson ++ "}"
  | .hyperbolicHandles s c =>
      "{\"count\":" ++ c.toJson ++ ",\"op\":\"HyperbolicHandles\",\"start_index\":"
        ++ natToString s ++ "}"
  | .auxiliary n d =>
      "{\"definition\":" ++ d.toJson ++ ",\"name\":" ++ jsonString n ++ ",\"op\":\"Auxiliary\"}"

/-- Comma-separated canonical JSON of a factor list. -/
def RawWord.listToJson : List RawWord → String
  | [] => ""
  | [w] => w.toJson
  | w :: ws => w.toJson ++ "," ++ RawWord.listToJson ws

end

/-- The canonical byte string of a word: `ast.canonical_json` after the constructor-level
canonicalization `ast.from_json` performs on load. -/
def canonicalJson (w : RawWord) : String := w.canon.toJson

/-- **The content hash**: SHA-256 of `canonicalJson w`, UTF-8 encoded.  This is
`dyadic_search.words.ast.content_hash`, and it is what the generated LaTeX carries in its
`% ast-hash:` trailer and `scripts/check_dyadic.sh`'s D4 check compares. -/
def astHash (w : RawWord) : String := Sha256.hex (canonicalJson w)

/-- Build-time gate: `#eval assertAstHash "name" w "<digest>"` prints the digest on
agreement and **fails elaboration** otherwise, so a tree edited without updating its hash
constant cannot build.  Also refuses a tree that is not well-formed, whose hash Python
would never have produced. -/
def assertAstHash (label : String) (w : RawWord) (expected : String) : IO Unit := do
  unless w.wf do
    throw <| IO.userError s!"WW5: {label} is not well-formed (RawWord.wf = false): an \
      empty name, an even etahat entry, or unsorted shadow parameters.  Python would \
      have rejected this tree, so its hash means nothing."
  let actual := astHash w
  if actual == expected then
    IO.println s!"WW5 ast-hash ok: {label} = {actual}"
  else
    throw <| IO.userError s!"WW5 ast-hash MISMATCH for {label}:\n  computed {actual}\n  \
      declared {expected}\nThe TeX and the Lean are not the same tree (merge gate 7 stop \
      condition).  Regenerate with `python3 scripts/dyadic_word_tex.py emit`."

/-! ## The bridge to `PWord`

`denote` is where the *derived* nodes are discharged: `orbitNorm` and `hyperbolicHandles`
are expanded (mirroring `ast.expand_orbit_norm` / `ast.expand_handles`), `auxiliary` is
inlined, `shadow` has no denotation.  The hash is taken **before** any of this.
-/

variable {Gen : Type*}

/-- What a `RawWord`'s free names denote: the alphabet map, the handle generators
`x_i` that `hyperbolicHandles` expands over, and the integer-parameter assignment.
Each is partial, and `denote` returns `none` on an unresolved name. -/
structure DenoteCtx (Gen : Type*) where
  /-- The generator named by a string. -/
  gen : String → Option Gen
  /-- The `i`-th handle generator (Python's `x<i>`). -/
  handleGen : Nat → Option Gen
  /-- The value of an integer parameter. -/
  param : String → Option Int

/-- Evaluate a symbolic exponent under a parameter assignment, mirroring
`ExponentExpr.evaluate`: `pow2` of a negative exponent is not an integer and is rejected,
as it is in Python.  Takes the assignment rather than the whole context, so that it stays
universe-free (`Option Int` and `Option (PWord Gen)` are different monads when `Gen`
lives above `Type 0`). -/
def RawExp.eval (ρ : String → Option Int) : RawExp → Option Int
  | .int n => some n
  | .param name => ρ name
  | .add l r => do pure ((← l.eval ρ) + (← r.eval ρ))
  | .sub l r => do pure ((← l.eval ρ) - (← r.eval ρ))
  | .mul l r => do pure ((← l.eval ρ) * (← r.eval ρ))
  | .pow2 e => do
      let k ← e.eval ρ
      if 0 ≤ k then pure (2 ^ k.toNat) else none

/-- The `ℤ̂`-exponent denoted by a finite spec: `Zhat.ofInt`, `ω₂`, or F2's `η̂`.
`GQ2.omega2` is spelled out: inside this namespace the bare name is the `RawSpec`
constructor. -/
noncomputable def RawSpec.toZhat : RawSpec → Zhat
  | .int n => Zhat.ofInt n
  | .omega2 => GQ2.omega2
  | .etahat num den => EtaData.toZhat ⟨num, den⟩

/-- `ast.expand_orbit_norm`: the displayed product `z^{U^1} · z^{U^2} ⋯ z^{U^m}`.
`m = 0` gives the empty product. -/
def orbitNormFactors (z u : PWord Gen) (m : Nat) : List (PWord Gen) :=
  (List.range m).map fun j => .conj z (.zpow u (j + 1 : ℤ))

/-- `ast.expand_handles`: `[x_s, x_{s+1}] · [x_{s+2}, x_{s+3}] ⋯`, over the handle
generators supplied by the context. -/
def handleFactors (c : DenoteCtx Gen) (start h : Nat) : Option (List (PWord Gen)) :=
  (List.range h).mapM fun j => do
    let u ← c.handleGen (start + 2 * j)
    let v ← c.handleGen (start + 2 * j + 1)
    pure (PWord.comm (.gen u) (.gen v))

mutual

/-- **The bridge**: the `PWord` denoted by a `RawWord`, or `none` when the tree names
something the semantic syntax cannot express — an unresolved generator or parameter, a
block whose length is symbolic or negative, or a `shadow` (whose semantics are owned by
simplification ticket S4.2 and are deliberately not invented here).

Blocks are expanded and auxiliaries inlined; the hash was taken on the unexpanded tree,
so this step never moves it. -/
noncomputable def denote (c : DenoteCtx Gen) : RawWord → Option (PWord Gen)
  | .generator name => (c.gen name).map .gen
  | .identity => some .one
  | .multiply fs => (denoteList c fs).map PWord.prodList
  | .inverse w => (denote c w).map .inv
  | .integerPower w e =>
      match denote c w, e.eval c.param with
      | some w', some k => some (.zpow w' k)
      | _, _ => none
  | .zhatPower w s => (denote c w).map fun w' => .profPow w' s.toZhat
  | .omega2Power w => (denote c w).map fun w' => .profPow w' GQ2.omega2
  | .conjugate w g =>
      match denote c w, denote c g with
      | some w', some g' => some (.conj w' g')
      | _, _ => none
  | .commutator l r =>
      match denote c l, denote c r with
      | some l', some r' => some (.comm l' r')
      | _, _ => none
  | .orbitNorm u m z =>
      match m.eval c.param, denote c z, denote c u with
      | some k, some z', some u' =>
          if 0 ≤ k then some (PWord.prodList (orbitNormFactors z' u' k.toNat)) else none
      | _, _, _ => none
  | .shadow _ _ _ => none
  | .hyperbolicHandles s cnt =>
      match cnt.eval c.param with
      | some k =>
          if 0 ≤ k then (handleFactors c s k.toNat).map PWord.prodList else none
      | none => none
  | .auxiliary _ d => denote c d

/-- `denote`, factorwise. -/
noncomputable def denoteList (c : DenoteCtx Gen) : List RawWord → Option (List (PWord Gen))
  | [] => some []
  | w :: ws =>
      match denote c w, denoteList c ws with
      | some a, some as => some (a :: as)
      | _, _ => none

end

/-! ## Cross-repo pins

Two of the five frozen selection rows (`artifacts/reports/selection-freeze.md`,
2026-07-31) are small enough to carry here as literal trees, and both are pinned twice:

* the tree → bytes step by `rfl`, in the **kernel**;
* the bytes → digest step by `#eval`, at elaboration time.

The digests are the ones stored in the simplification campaign's own certificates, so a
green build of this file is a cross-repo agreement, not a self-consistency check.  The
remaining three rows arrive with their wave-2 word tickets; their digests are recorded in
`frozenRowHashes` so that a words file cannot invent one.
-/

/-- **Frozen row 1** (type `L`, `n = 1`): the stabilized square commutator
`(x₀^σ)⁻¹ (x₀⁻³τ)^{ω₂} x₁² [x₁, x₁^{σ₂}]`, certificate `L-sq-n1-v001`.  This is also the
simplification campaign's golden tree 1 (`test_words_ast.square_commutator_word`). -/
def frozenLsqN1 : RawWord :=
  .multiply [
    .inverse (.conjugate (.generator "x0") (.generator "sigma")),
    .auxiliary "a" (.omega2Power (.multiply [
      .integerPower (.generator "x0") (.int (-3)), .generator "tau"])),
    .integerPower (.generator "x1") (.int 2),
    .auxiliary "c" (.commutator (.generator "x1")
      (.auxiliary "y1" (.conjugate (.generator "x1")
        (.auxiliary "sigma2" (.omega2Power (.generator "sigma"))))))]

/-- **Frozen row 2** (compact `N`, `α = 2`, `h = 0`):
`x₀^{2+2^α} [x₀,x₁] · x₂^{-σ} (x₂τ)^{ω₂} · H_h`, certificate `N-compact-alpha2-h0-v001`.
Note `x₂^{-σ}` is `inverse (conjugate …)` and never a `-σ` exponent (packet Rem. 2.3). -/
def frozenNCompactAlpha2H0 : RawWord :=
  .multiply [
    .integerPower (.generator "x0") (.int 6),
    .commutator (.generator "x0") (.generator "x1"),
    .inverse (.conjugate (.generator "x2") (.generator "sigma")),
    .omega2Power (.multiply [.generator "x2", .generator "tau"]),
    .hyperbolicHandles 3 (.int 0)]


/-! ### Layer pins

Every step of the serialization, pinned in the kernel on a minimal input.  They are cheap
and they localize a regression: if the whole-tree pins below break, exactly one of these
breaks with them, and it names the layer. -/

/-- The number renderer agrees with CPython's (`-3`, not `- 3` or `−3`). -/
example : intToString (-3) = "-3" ∧ intToString 0 = "0" ∧ natToString 12 = "12" := by
  refine ⟨rfl, rfl, rfl⟩

/-- String escaping, on a name that needs none. -/
example : jsonString "x0" = "\"x0\"" := by rfl

/-- Escaping of the two characters CPython backslash-escapes, and of a non-ASCII
codepoint (`ensure_ascii=True` turns `η` into `η`). -/
example : jsonString "a\"b\\cη" = "\"a\\\"b\\\\c\\u03b7\"" := by rfl

/-- An exponent expression. -/
example : RawExp.toJson (.int (-3)) = "{\"type\":\"Int\",\"value\":-3}" := by rfl

/-- The S1.M canonicalization, in the kernel: `EtaHat(3, 9)` *is* `EtaHat(1, 3)`. -/
example : RawSpec.canon (.etahat 3 9) = .etahat 1 3 := by rfl

/-- A leaf word node. -/
example : RawWord.toJson (.generator "x0") = "{\"name\":\"x0\",\"op\":\"Generator\"}" := by
  rfl

/-- The nested-list case (`Multiply`), which is where the mutual recursion lives. -/
example : RawWord.toJson (.multiply [.identity])
    = "{\"children\":[{\"op\":\"Identity\"}],\"op\":\"Multiply\"}" := by rfl

/-- A block node, including its `Nat` field. -/
example : canonicalJson (.hyperbolicHandles 3 (.int 0))
    = "{\"count\":{\"type\":\"Int\",\"value\":0},\"op\":\"HyperbolicHandles\",\
      \"start_index\":3}" := by
  rfl

/-- `shadow` has no denotation — simplification ticket S4.2 owns its semantics, and
inventing one here is exactly what the ledger forbids. -/
example (c : DenoteCtx Unit) (k : String) (ps : List (String × RawParam)) (w : RawWord) :
    denote c (.shadow k ps w) = none := by rfl

-- The `rfl` pins below unfold a whole tree into a string literal; the default recursion
-- depth is not enough for a word of this size.  This raises only the elaborator's stack
-- budget, never `maxHeartbeats`, and adds no axiom.
set_option maxRecDepth 8000

/-- The canonical bytes of frozen row 1, pinned in the kernel. -/
theorem canonicalJson_frozenLsqN1 :
    canonicalJson frozenLsqN1 =
      "{\"children\":[{\"op\":\"Inverse\",\"word\":{\"conjugator\":{\"name\":\"sigma\",\"op\
      \":\"Generator\"},\"op\":\"Conjugate\",\"word\":{\"name\":\"x0\",\"op\":\"Generator\"\
      }}},{\"definition\":{\"op\":\"Omega2Power\",\"word\":{\"children\":[{\"exponent\":{\"\
      type\":\"Int\",\"value\":-3},\"op\":\"IntegerPower\",\"word\":{\"name\":\"x0\",\"op\"\
      :\"Generator\"}},{\"name\":\"tau\",\"op\":\"Generator\"}],\"op\":\"Multiply\"}},\"nam\
      e\":\"a\",\"op\":\"Auxiliary\"},{\"exponent\":{\"type\":\"Int\",\"value\":2},\"op\":\
      \"IntegerPower\",\"word\":{\"name\":\"x1\",\"op\":\"Generator\"}},{\"definition\":{\"\
      left\":{\"name\":\"x1\",\"op\":\"Generator\"},\"op\":\"Commutator\",\"right\":{\"defi\
      nition\":{\"conjugator\":{\"definition\":{\"op\":\"Omega2Power\",\"word\":{\"name\":\
      \"sigma\",\"op\":\"Generator\"}},\"name\":\"sigma2\",\"op\":\"Auxiliary\"},\"op\":\"C\
      onjugate\",\"word\":{\"name\":\"x1\",\"op\":\"Generator\"}},\"name\":\"y1\",\"op\":\"\
      Auxiliary\"}},\"name\":\"c\",\"op\":\"Auxiliary\"}],\"op\":\"Multiply\"}" := by
  rfl

/-- The canonical bytes of frozen row 2, pinned in the kernel. -/
theorem canonicalJson_frozenNCompactAlpha2H0 :
    canonicalJson frozenNCompactAlpha2H0 =
      "{\"children\":[{\"exponent\":{\"type\":\"Int\",\"value\":6},\"op\":\"IntegerPower\",\
      \"word\":{\"name\":\"x0\",\"op\":\"Generator\"}},{\"left\":{\"name\":\"x0\",\"op\":\"\
      Generator\"},\"op\":\"Commutator\",\"right\":{\"name\":\"x1\",\"op\":\"Generator\"}},\
      {\"op\":\"Inverse\",\"word\":{\"conjugator\":{\"name\":\"sigma\",\"op\":\"Generator\"\
      },\"op\":\"Conjugate\",\"word\":{\"name\":\"x2\",\"op\":\"Generator\"}}},{\"op\":\"Om\
      ega2Power\",\"word\":{\"children\":[{\"name\":\"x2\",\"op\":\"Generator\"},{\"name\":\
      \"tau\",\"op\":\"Generator\"}],\"op\":\"Multiply\"}},{\"count\":{\"type\":\"Int\",\"v\
      alue\":0},\"op\":\"HyperbolicHandles\",\"start_index\":3}],\"op\":\"Multiply\"}" := by
  rfl

/-- Both frozen rows are well-formed, in the kernel. -/
theorem wf_frozen : frozenLsqN1.wf = true ∧ frozenNCompactAlpha2H0.wf = true := by
  constructor <;> rfl

/-- The digests of the frozen selection rows that carry one
(`artifacts/reports/selection-freeze.md`, 2026-07-31).  Row 3 (noncompact `N`) is absent
on purpose: its certificates are still `experimental` and the freeze doc lists no hash.
A wave-2 words file must reproduce its row's digest here, not invent one. -/
def frozenRowHashes : List (String × String) :=
  [("L (L-sq-n1-v001)", "d129037ce96177524c5798cbe0c13d7844ab513d136360d1270dbd89e81051cb"),
   ("N0 (N-compact-alpha2-h0-v001)",
     "a940b6ad06d9728a6b0b5d20f27c76994d83103e65accc6b844fe6174755fc10"),
   ("M0 (M-compact-alpha2-h0-q2-v001)",
     "7c9005f50f9e1d5ddfa8880a3a3168d1a47661efdaae81339ab968055bbf036a"),
   ("Mpc (M-procyclic-alpha2-r1-eps1-eta1-h0-q2-v001)",
     "55b24a4b141274bc30d09468096f4fa021184c5dc22c17823e423457928a26cf")]

/-- Build-time check of the SHA-256 implementation itself, on FIPS 180-4's test vectors:
the empty string, the one-block `"abc"`, and the two-block 56-character message (which
exercises the padding's block boundary). -/
def assertSha256Vectors : IO Unit := do
  let vectors : List (String × String) :=
    [("", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
     ("abc", "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
     ("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
       "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1")]
  for (input, expected) in vectors do
    let actual := Sha256.hex input
    if actual != expected then
      throw <| IO.userError s!"WW5: SHA-256 is wrong on the FIPS 180-4 vector \
        {repr input}: computed {actual}, expected {expected}"
  IO.println s!"WW5 sha256 ok: {vectors.length} FIPS 180-4 vectors"

#eval assertSha256Vectors

/-! ### The gate-A constants

`<declaration>_astHash` is `pretty_lean.py`'s naming convention (`HASH_SUFFIX`), and it is
what `scripts/dyadic_word_tex.py check` greps for in the Lean module a manifest entry
names.  A wave-2 words file declares exactly this pair — the constant and the `#eval`
guard — for each of its words.  The `#eval` is what makes the constant honest: it
recomputes the digest from the tree, so the constant cannot drift. -/

/-- Gate-A hash of `frozenLsqN1`, as stored in certificate `L-sq-n1-v001`. -/
def frozenLsqN1_astHash : String :=
  "d129037ce96177524c5798cbe0c13d7844ab513d136360d1270dbd89e81051cb"

/-- Gate-A hash of `frozenNCompactAlpha2H0`, as stored in certificate
`N-compact-alpha2-h0-v001`. -/
def frozenNCompactAlpha2H0_astHash : String :=
  "a940b6ad06d9728a6b0b5d20f27c76994d83103e65accc6b844fe6174755fc10"

-- The two cross-repo pins.  A mismatch here fails the build.
#eval assertAstHash "frozen row L (L-sq-n1-v001)" frozenLsqN1 frozenLsqN1_astHash

#eval assertAstHash "frozen row N0 (N-compact-alpha2-h0-v001)" frozenNCompactAlpha2H0
  frozenNCompactAlpha2H0_astHash

end GQ2.Dyadic.Export

