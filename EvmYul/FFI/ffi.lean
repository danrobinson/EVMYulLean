import Init.Data.Array.Lemmas

namespace ffi

@[extern "sha256"]
opaque sha256 (input : @& ByteArray) (len : USize) : ByteArray

def SHA256 (d : ByteArray) : Except String ByteArray :=
  pure <| sha256 d d.size.toUSize

@[extern "blake2compressb64"]
opaque BLAKE2Compress (input : @& ByteArray) : ByteArray

def BLAKE2 (d : ByteArray) : Except String ByteArray := do
  if d.size != 213                    then throw "error"
  if d[212]! ∉ [0, 1].map Nat.toUInt8 then throw "error"
  return BLAKE2Compress d

@[extern "memset_zero"]
def ByteArray.zeroes (n : USize) : ByteArray :=
  ⟨Array.replicate n.toNat 0⟩

@[simp] theorem ByteArray.size_zeroes (n : USize) :
    (ByteArray.zeroes n).size = n.toNat := by
  change (Array.replicate n.toNat 0).size = n.toNat
  simp

@[simp] theorem ByteArray.getElem_zeroes
    (n : USize) (index : Nat)
    (hIndex : index < (ByteArray.zeroes n).size) :
    (ByteArray.zeroes n)[index] = 0 := by
  rw [ByteArray.size_zeroes] at hIndex
  change
    (Array.replicate n.toNat 0)[index]'(by simpa using hIndex) = 0
  simp

@[simp] theorem ByteArray.data_getD_zeroes
    (n : USize) (index : Nat) :
    (ByteArray.zeroes n).data.getD index 0 = 0 := by
  simp [ByteArray.zeroes, Array.getD]

@[simp] theorem ByteArray.data_getElem?_zeroes
    (n : USize) (index : Nat) :
    (ByteArray.zeroes n).data[index]? =
      if index < n.toNat then some 0 else none := by
  simp [ByteArray.zeroes, Array.getElem?_replicate]

@[extern "keccak256"]
opaque keccak256 (input : @& ByteArray) (len : USize) : ByteArray

def KECCAK256 (d : ByteArray) : Except String ByteArray :=
  pure <| keccak256 d d.size.toUSize

def KEC (data : ByteArray) : ByteArray :=
  ffi.KECCAK256 data |>.toOption.getD .empty

end ffi
