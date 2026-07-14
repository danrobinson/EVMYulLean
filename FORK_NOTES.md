# Fork notes: how this fork differs from NethermindEth/EVMYulLean

This fork of [NethermindEth/EVMYulLean](https://github.com/NethermindEth/EVMYulLean)
is the pinned semantic trust anchor for the
[Solidus](https://github.com/paradigmxyz/solidus) verified Yul → EVM compiler:
Solidus's correctness theorem interprets Yul source with this repository's Yul
interpreter and EVM bytecode with this repository's EVM semantics. Because any
edit to this repository moves the goalposts of that theorem, this file
discloses every way the fork diverges from upstream and which differences sit
inside the trusted base. The fork range is upstream `047f630..` this branch
(28 commits as of the `b08573c` pin).

The one-line summary: the fork adds **zero axioms and zero sorries**, removes
no upstream checks or tests, and its semantic changes either fix upstream
interpreter bugs (bringing behavior *closer* to the official Yul specification
and the Yellow Paper/EIPs) or implement previously-stubbed features. The items
below are the ones a careful auditor should know about anyway.

## 1. Shared Yul/EVM specification surface

Several fork commits make the Yul interpreter and the EVM semantics consume
the *same* definitions instead of two parallel copies:

- `runPrecompiledContract` and the `Ξ_*` precompile implementations
  (`EvmYul/EVM/PrecompiledContracts.lean`);
- `PrecompiledContract` / `ofAddress?` precompile-address classification
  (`EvmYul/State/Account.lean`);
- `toExecute` address → (precompile | code) dispatch
  (`EvmYul/Maps/AccountMap.lean`); the `.EVM` branch additionally resolves
  EIP-7702 delegation designators, the `.Yul` branch does not;
- `MachineState.finishExternalCall` — post-call output copy, returndata,
  memory-expansion accounting (`EvmYul/MachineStateOps.lean`);
- `EVM.Ccallgas` and its helpers — the 63/64 forwarding rule and call stipend
  (`EvmYul/EVM/Gas.lean`);
- `emptyAccount` / `dead` (EIP-161) and the `extCodeSize` / `extCodeHash` /
  `extCodeCopy'` external-code-inspection skeleton.

This is deliberate one-spec/two-consumers factoring, and each shared
definition was checked against the Yellow Paper rule it implements. But be
aware of the consequence: **for exactly these computations, a Yul↔EVM
equivalence theorem holds by shared definition, not by independent proof.**
They are part of the trusted specification, like every other line of this
repository.

Conversely, the value-transfer preludes are intentionally *duplicated*, not
shared (`thetaCallTransfer` on the EVM side vs. `callTransferAccountMap?` on
the Yul side), so the theorem does independently relate them; keep them in
sync when editing.

## 2. The `keccak256` native/pure boundary

Upstream declared `keccak256` as an `opaque` constant with `@[extern]` — no
logical content at all. This fork gives it a total pure-Lean Keccak-f[1600]
sponge as its logical body (`EvmYul/SpongeHash/Keccak256.lean`) while keeping
`@[extern "keccak256"]` for compiled execution (`EvmYul/FFI/ffi.lean`).

Consequence: Lean proofs constrain the pure sponge; the compiled binary runs
the native C implementation. Byte-parity between the two is asserted by
runtime self-tests and downstream test witnesses, **not proven in-tree**. A
divergence could make concrete executions disagree with the theorem's model,
but cannot make the theorem false. The same pattern applies (trivially) to
`ByteArray.zeroes` / `memset_zero`. `sha256` and `blake2compressb64` remain
opaque externs as upstream had them.

## 3. Hardfork pinning: Fusaka MODEXP, no version gates

The MODEXP precompile implements the Fusaka rules unconditionally — EIP-7883
repricing (min 500 gas, revised complexity formula) and EIP-7823 input-length
limits (1024-byte base/exponent/modulus caps). Pre-Fusaka MODEXP behavior is
**not** modeled. Likewise CLZ (EIP-7939) and EIP-7702 delegation lookup are
present without fork gating on this repository's side (downstream consumers
apply their own version gating).

## 4. Yul-side gas is threaded, not charged

The Yul interpreter forwards call gas to child frames (`EVM.Ccallgas` →
`freshExternalCall`) so that sub-call semantics are frame-accurate, but Yul
execution itself does not charge gas per operation. Gas-sensitive claims are
the EVM side's business.

## 5. The `isEmpty` merge sentinel

`restoreSuccessfulContractCallState` (and the precompile analogue) keeps the
caller's `accountMap`/`substate` when a successful child returns an *empty*
account map. This mirrors the Yellow Paper's `σ'' = ∅` abort sentinel and is
expected to be unreachable on genuinely successful calls; see the docstring
in `EvmYul/Yul/Interpreter.lean` for the invariant and the (harmless)
`createdAccounts` asymmetry.

## 6. Minor mechanical notes

- Two `native_decide` uses in `EvmYul/UInt256.lean` prove the fixed numeric
  fact `2 ^ 8 = UInt8.size` inside private byte-conversion lemmas; they add
  `Lean.ofReduceBool` to those two lemmas' axiom footprints only.
- The Lean toolchain was bumped v4.22.0 → v4.28.0 with matching official
  Mathlib/batteries/etc. bumps; no dependency was replaced by a fork, and the
  lake manifest pins exact commit hashes.
- The new `EvmYul/Yul/YulSemanticsTests/Main.lean` suite encodes
  official-Yul-spec outcomes (switch selects exactly the matching case,
  callee `revert` returns 0 to the caller, `selfdestruct` halts, block
  scoping/no-shadowing, zero-initialized return variables); several of these
  tests fail against the upstream interpreter, which is why the corresponding
  interpreter fixes exist.

## Summary of semantic changes vs. upstream

Yul interpreter fixes (each toward the official Yul spec): switch executes
exactly the matching case with no side effects from non-taken branches;
omitted switch default is a no-op (upstream synthesized a spurious `break`);
callee `revert` rolls back the child's state, delivers revert data, and
returns 0 to the *continuing* caller (upstream aborted the caller); external
CALL/STATICCALL executes the callee's code (upstream ran the caller's);
`selfdestruct` halts the current context; `leave` inside a for-loop body/post
exits the function; block-scoped variables, no shadowing,
assignment-requires-declaration, zero-initialized return variables;
RETURNDATACOPY is bounds-checked (EIP-211); EXTCODESIZE/COPY/HASH implemented
(upstream stubbed them as errors); precompile dispatch and depth-limit/value
checks aligned with the EVM side; EIP-2929 target warming applied before
dispatch and preserved across child revert.

EVM-side fixes/additions (each checked against the cited rule): PUSH
immediates past end-of-code zero-pad (Yellow Paper); MODEXP no longer
truncates >32-byte bases; Fusaka MODEXP (EIP-7883/EIP-7823); CLZ (EIP-7939);
EIP-7702 delegation lookup with EXTCODE* observing the raw designator;
EIP-6780 selfdestruct refactor (behavior preserved); RETURNDATACOPY bounds
(EIP-211); `D_J` jump-destination analysis totalized by structural recursion
on remaining code size (bit-identical behavior, no fuel that can run out);
keccak256 given a genuine pure Keccak-f[1600] logical definition.
