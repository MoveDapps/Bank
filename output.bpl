
// ** Expanded prelude

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Basic theory for vectors using arrays. This version of vectors is not extensional.

type {:datatype} Vec _;

function {:constructor} Vec<T>(v: [int]T, l: int): Vec T;

function {:builtin "MapConst"} MapConstVec<T>(T): [int]T;
function DefaultVecElem<T>(): T;
function {:inline} DefaultVecMap<T>(): [int]T { MapConstVec(DefaultVecElem()) }

function {:inline} EmptyVec<T>(): Vec T {
    Vec(DefaultVecMap(), 0)
}

function {:inline} MakeVec1<T>(v: T): Vec T {
    Vec(DefaultVecMap()[0 := v], 1)
}

function {:inline} MakeVec2<T>(v1: T, v2: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2], 2)
}

function {:inline} MakeVec3<T>(v1: T, v2: T, v3: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2][2 := v3], 3)
}

function {:inline} MakeVec4<T>(v1: T, v2: T, v3: T, v4: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2][2 := v3][3 := v4], 4)
}

function {:inline} ExtendVec<T>(v: Vec T, elem: T): Vec T {
    (var l := l#Vec(v);
    Vec(v#Vec(v)[l := elem], l + 1))
}

function {:inline} ReadVec<T>(v: Vec T, i: int): T {
    v#Vec(v)[i]
}

function {:inline} LenVec<T>(v: Vec T): int {
    l#Vec(v)
}

function {:inline} IsEmptyVec<T>(v: Vec T): bool {
    l#Vec(v) == 0
}

function {:inline} RemoveVec<T>(v: Vec T): Vec T {
    (var l := l#Vec(v) - 1;
    Vec(v#Vec(v)[l := DefaultVecElem()], l))
}

function {:inline} RemoveAtVec<T>(v: Vec T, i: int): Vec T {
    (var l := l#Vec(v) - 1;
    Vec(
        (lambda j: int ::
           if j >= 0 && j < l then
               if j < i then v#Vec(v)[j] else v#Vec(v)[j+1]
           else DefaultVecElem()),
        l))
}

function {:inline} ConcatVec<T>(v1: Vec T, v2: Vec T): Vec T {
    (var l1, m1, l2, m2 := l#Vec(v1), v#Vec(v1), l#Vec(v2), v#Vec(v2);
    Vec(
        (lambda i: int ::
          if i >= 0 && i < l1 + l2 then
            if i < l1 then m1[i] else m2[i - l1]
          else DefaultVecElem()),
        l1 + l2))
}

function {:inline} ReverseVec<T>(v: Vec T): Vec T {
    (var l := l#Vec(v);
    Vec(
        (lambda i: int :: if 0 <= i && i < l then v#Vec(v)[l - i - 1] else DefaultVecElem()),
        l))
}

function {:inline} SliceVec<T>(v: Vec T, i: int, j: int): Vec T {
    (var m := v#Vec(v);
    Vec(
        (lambda k:int ::
          if 0 <= k && k < j - i then
            m[i + k]
          else
            DefaultVecElem()),
        (if j - i < 0 then 0 else j - i)))
}


function {:inline} UpdateVec<T>(v: Vec T, i: int, elem: T): Vec T {
    Vec(v#Vec(v)[i := elem], l#Vec(v))
}

function {:inline} SwapVec<T>(v: Vec T, i: int, j: int): Vec T {
    (var m := v#Vec(v);
    Vec(m[i := m[j]][j := m[i]], l#Vec(v)))
}

function {:inline} ContainsVec<T>(v: Vec T, e: T): bool {
    (var l := l#Vec(v);
    (exists i: int :: InRangeVec(v, i) && v#Vec(v)[i] == e))
}

function IndexOfVec<T>(v: Vec T, e: T): int;
axiom {:ctor "Vec"} (forall<T> v: Vec T, e: T :: {IndexOfVec(v, e)}
    (var i := IndexOfVec(v,e);
     if (!ContainsVec(v, e)) then i == -1
     else InRangeVec(v, i) && ReadVec(v, i) == e &&
        (forall j: int :: j >= 0 && j < i ==> ReadVec(v, j) != e)));

// This function should stay non-inlined as it guards many quantifiers
// over vectors. It appears important to have this uninterpreted for
// quantifier triggering.
function InRangeVec<T>(v: Vec T, i: int): bool {
    i >= 0 && i < LenVec(v)
}

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Boogie model for multisets, based on Boogie arrays. This theory assumes extensional equality for element types.

type {:datatype} Multiset _;
function {:constructor} Multiset<T>(v: [T]int, l: int): Multiset T;

function {:builtin "MapConst"} MapConstMultiset<T>(l: int): [T]int;

function {:inline} EmptyMultiset<T>(): Multiset T {
    Multiset(MapConstMultiset(0), 0)
}

function {:inline} LenMultiset<T>(s: Multiset T): int {
    l#Multiset(s)
}

function {:inline} ExtendMultiset<T>(s: Multiset T, v: T): Multiset T {
    (var len := l#Multiset(s);
    (var cnt := v#Multiset(s)[v];
    Multiset(v#Multiset(s)[v := (cnt + 1)], len + 1)))
}

// This function returns (s1 - s2). This function assumes that s2 is a subset of s1.
function {:inline} SubtractMultiset<T>(s1: Multiset T, s2: Multiset T): Multiset T {
    (var len1 := l#Multiset(s1);
    (var len2 := l#Multiset(s2);
    Multiset((lambda v:T :: v#Multiset(s1)[v]-v#Multiset(s2)[v]), len1-len2)))
}

function {:inline} IsEmptyMultiset<T>(s: Multiset T): bool {
    (l#Multiset(s) == 0) &&
    (forall v: T :: v#Multiset(s)[v] == 0)
}

function {:inline} IsSubsetMultiset<T>(s1: Multiset T, s2: Multiset T): bool {
    (l#Multiset(s1) <= l#Multiset(s2)) &&
    (forall v: T :: v#Multiset(s1)[v] <= v#Multiset(s2)[v])
}

function {:inline} ContainsMultiset<T>(s: Multiset T, v: T): bool {
    v#Multiset(s)[v] > 0
}

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Theory for tables.

type {:datatype} Table _ _;

// v is the SMT array holding the key-value assignment. e is an array which
// independently determines whether a key is valid or not. l is the length.
//
// Note that even though the program cannot reflect over existence of a key,
// we want the specification to be able to do this, so it can express
// verification conditions like "key has been inserted".
function {:constructor} Table<K, V>(v: [K]V, e: [K]bool, l: int): Table K V;

// Functions for default SMT arrays. For the table values, we don't care and
// use an uninterpreted function.
function DefaultTableArray<K, V>(): [K]V;
function DefaultTableKeyExistsArray<K>(): [K]bool;
axiom DefaultTableKeyExistsArray() == (lambda i: int :: false);

function {:inline} EmptyTable<K, V>(): Table K V {
    Table(DefaultTableArray(), DefaultTableKeyExistsArray(), 0)
}

function {:inline} GetTable<K,V>(t: Table K V, k: K): V {
    // Notice we do not check whether key is in the table. The result is undetermined if it is not.
    v#Table(t)[k]
}

function {:inline} LenTable<K,V>(t: Table K V): int {
    l#Table(t)
}


function {:inline} ContainsTable<K,V>(t: Table K V, k: K): bool {
    e#Table(t)[k]
}

function {:inline} UpdateTable<K,V>(t: Table K V, k: K, v: V): Table K V {
    Table(v#Table(t)[k := v], e#Table(t)[k := true], l#Table(t))
}

function {:inline} AddTable<K,V>(t: Table K V, k: K, v: V): Table K V {
    // This function has an undetermined result if the key is already in the table
    // (all specification functions have this "partial definiteness" behavior). Thus we can
    // just increment the length.
    Table(v#Table(t)[k := v], e#Table(t)[k := true], l#Table(t) + 1)
}

function {:inline} RemoveTable<K,V>(t: Table K V, k: K): Table K V {
    // Similar as above, we only need to consider the case where the key is in the table.
    Table(v#Table(t), e#Table(t)[k := false], l#Table(t) - 1)
}
// Copyright (c) 2022, Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

// ==================================================================================
// Native transfer// ----------------------------------------------------------------------------------
// Native transfer implementation for object type `$0_market_AdminCap`


procedure {:inline 1} $2_transfer_transfer_internal'$0_market_AdminCap'(obj: $0_market_AdminCap, recipient: int, to_object: bool);

procedure {:inline 1} $2_transfer_share_object'$0_market_AdminCap'(obj: $0_market_AdminCap);

procedure {:inline 1} $2_transfer_freeze_object'$0_market_AdminCap'(obj: $0_market_AdminCap);// ----------------------------------------------------------------------------------
// Native transfer implementation for object type `$0_market_BorrowRecord'#0_#1'`


procedure {:inline 1} $2_transfer_transfer_internal'$0_market_BorrowRecord'#0_#1''(obj: $0_market_BorrowRecord'#0_#1', recipient: int, to_object: bool);

procedure {:inline 1} $2_transfer_share_object'$0_market_BorrowRecord'#0_#1''(obj: $0_market_BorrowRecord'#0_#1');

procedure {:inline 1} $2_transfer_freeze_object'$0_market_BorrowRecord'#0_#1''(obj: $0_market_BorrowRecord'#0_#1');// ----------------------------------------------------------------------------------
// Native transfer implementation for object type `$0_market_Market`


procedure {:inline 1} $2_transfer_transfer_internal'$0_market_Market'(obj: $0_market_Market, recipient: int, to_object: bool);

procedure {:inline 1} $2_transfer_share_object'$0_market_Market'(obj: $0_market_Market);

procedure {:inline 1} $2_transfer_freeze_object'$0_market_Market'(obj: $0_market_Market);// ----------------------------------------------------------------------------------
// Native transfer implementation for object type `$0_market_SubMarket'#0'`


procedure {:inline 1} $2_transfer_transfer_internal'$0_market_SubMarket'#0''(obj: $0_market_SubMarket'#0', recipient: int, to_object: bool);

procedure {:inline 1} $2_transfer_share_object'$0_market_SubMarket'#0''(obj: $0_market_SubMarket'#0');

procedure {:inline 1} $2_transfer_freeze_object'$0_market_SubMarket'#0''(obj: $0_market_SubMarket'#0');

// ==================================================================================
// Native object

procedure {:inline 1} $2_object_bytes_to_address(bytes: Vec (int)) returns (res: int);// ----------------------------------------------------------------------------------
// Native id implementation for object type `$0_market_Market`


procedure {:inline 1} $2_object_get_info'$0_market_Market'(obj: $0_market_Market) returns (res: $2_object_Info);

procedure {:inline 1} $2_object_delete_impl'$0_market_Market'(info: $0_market_Market);// ----------------------------------------------------------------------------------
// Native id implementation for object type `$2_object_UID`


procedure {:inline 1} $2_object_get_info'$2_object_UID'(obj: $2_object_UID) returns (res: $2_object_Info);

procedure {:inline 1} $2_object_delete_impl'$2_object_UID'(info: $2_object_UID);

// ==================================================================================
// Native tx_context

procedure {:inline 1} $2_tx_context_derive_id(tx_hash: Vec (int), ids_created: int) returns (res: int);

// ==================================================================================
// Native event


// ============================================================================================
// Primitive Types

const $MAX_U8: int;
axiom $MAX_U8 == 255;
const $MAX_U64: int;
axiom $MAX_U64 == 18446744073709551615;
const $MAX_U128: int;
axiom $MAX_U128 == 340282366920938463463374607431768211455;

type {:datatype} $Range;
function {:constructor} $Range(lb: int, ub: int): $Range;

function {:inline} $IsValid'bool'(v: bool): bool {
  true
}

function $IsValid'u8'(v: int): bool {
  v >= 0 && v <= $MAX_U8
}

function $IsValid'u64'(v: int): bool {
  v >= 0 && v <= $MAX_U64
}

function $IsValid'u128'(v: int): bool {
  v >= 0 && v <= $MAX_U128
}

function $IsValid'num'(v: int): bool {
  true
}

function $IsValid'address'(v: int): bool {
  // TODO: restrict max to representable addresses?
  v >= 0
}

function {:inline} $IsValidRange(r: $Range): bool {
   $IsValid'u64'(lb#$Range(r)) &&  $IsValid'u64'(ub#$Range(r))
}

// Intentionally not inlined so it serves as a trigger in quantifiers.
function $InRange(r: $Range, i: int): bool {
   lb#$Range(r) <= i && i < ub#$Range(r)
}


function {:inline} $IsEqual'u8'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u64'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u128'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'num'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'address'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'bool'(x: bool, y: bool): bool {
    x == y
}

// ============================================================================================
// Memory

type {:datatype} $Location;

// A global resource location within the statically known resource type's memory,
// where `a` is an address.
function {:constructor} $Global(a: int): $Location;

// A local location. `i` is the unique index of the local.
function {:constructor} $Local(i: int): $Location;

// The location of a reference outside of the verification scope, for example, a `&mut` parameter
// of the function being verified. References with these locations don't need to be written back
// when mutation ends.
function {:constructor} $Param(i: int): $Location;


// A mutable reference which also carries its current value. Since mutable references
// are single threaded in Move, we can keep them together and treat them as a value
// during mutation until the point they are stored back to their original location.
type {:datatype} $Mutation _;
function {:constructor} $Mutation<T>(l: $Location, p: Vec int, v: T): $Mutation T;

// Representation of memory for a given type.
type {:datatype} $Memory _;
function {:constructor} $Memory<T>(domain: [int]bool, contents: [int]T): $Memory T;

function {:builtin "MapConst"} $ConstMemoryDomain(v: bool): [int]bool;
function {:builtin "MapConst"} $ConstMemoryContent<T>(v: T): [int]T;
axiom $ConstMemoryDomain(false) == (lambda i: int :: false);
axiom $ConstMemoryDomain(true) == (lambda i: int :: true);


// Dereferences a mutation.
function {:inline} $Dereference<T>(ref: $Mutation T): T {
    v#$Mutation(ref)
}

// Update the value of a mutation.
function {:inline} $UpdateMutation<T>(m: $Mutation T, v: T): $Mutation T {
    $Mutation(l#$Mutation(m), p#$Mutation(m), v)
}

function {:inline} $ChildMutation<T1, T2>(m: $Mutation T1, offset: int, v: T2): $Mutation T2 {
    $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), offset), v)
}

// Return true of the mutation is a parent of a child which was derived with the given edge offset. This
// is used to implement write-back choices.
function {:inline} $IsParentMutation<T1, T2>(parent: $Mutation T1, edge: int, child: $Mutation T2 ): bool {
    l#$Mutation(parent) == l#$Mutation(child) &&
    (var pp := p#$Mutation(parent);
    (var cp := p#$Mutation(child);
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
     cl == pl + 1 &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) ==  ReadVec(cp, i)) &&
     $EdgeMatches(ReadVec(cp, pl), edge)
    ))))
}

// Return true of the mutation is a parent of a child, for hyper edge.
function {:inline} $IsParentMutationHyper<T1, T2>(parent: $Mutation T1, hyper_edge: Vec int, child: $Mutation T2 ): bool {
    l#$Mutation(parent) == l#$Mutation(child) &&
    (var pp := p#$Mutation(parent);
    (var cp := p#$Mutation(child);
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
    (var el := LenVec(hyper_edge);
     cl == pl + el &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) == ReadVec(cp, i)) &&
     (forall i: int:: i >= 0 && i < el ==> $EdgeMatches(ReadVec(cp, pl + i), ReadVec(hyper_edge, i)))
    )))))
}

function {:inline} $EdgeMatches(edge: int, edge_pattern: int): bool {
    edge_pattern == -1 // wildcard
    || edge_pattern == edge
}



function {:inline} $SameLocation<T1, T2>(m1: $Mutation T1, m2: $Mutation T2): bool {
    l#$Mutation(m1) == l#$Mutation(m2)
}

function {:inline} $HasGlobalLocation<T>(m: $Mutation T): bool {
    is#$Global(l#$Mutation(m))
}

function {:inline} $HasLocalLocation<T>(m: $Mutation T, idx: int): bool {
    l#$Mutation(m) == $Local(idx)
}

function {:inline} $GlobalLocationAddress<T>(m: $Mutation T): int {
    a#$Global(l#$Mutation(m))
}



// Tests whether resource exists.
function {:inline} $ResourceExists<T>(m: $Memory T, addr: int): bool {
    domain#$Memory(m)[addr]
}

// Obtains Value of given resource.
function {:inline} $ResourceValue<T>(m: $Memory T, addr: int): T {
    contents#$Memory(m)[addr]
}

// Update resource.
function {:inline} $ResourceUpdate<T>(m: $Memory T, a: int, v: T): $Memory T {
    $Memory(domain#$Memory(m)[a := true], contents#$Memory(m)[a := v])
}

// Remove resource.
function {:inline} $ResourceRemove<T>(m: $Memory T, a: int): $Memory T {
    $Memory(domain#$Memory(m)[a := false], contents#$Memory(m))
}

// Copies resource from memory s to m.
function {:inline} $ResourceCopy<T>(m: $Memory T, s: $Memory T, a: int): $Memory T {
    $Memory(domain#$Memory(m)[a := domain#$Memory(s)[a]],
            contents#$Memory(m)[a := contents#$Memory(s)[a]])
}



// ============================================================================================
// Abort Handling

var $abort_flag: bool;
var $abort_code: int;

function {:inline} $process_abort_code(code: int): int {
    code
}

const $EXEC_FAILURE_CODE: int;
axiom $EXEC_FAILURE_CODE == -1;

// TODO(wrwg): currently we map aborts of native functions like those for vectors also to
//   execution failure. This may need to be aligned with what the runtime actually does.

procedure {:inline 1} $ExecFailureAbort() {
    $abort_flag := true;
    $abort_code := $EXEC_FAILURE_CODE;
}

procedure {:inline 1} $Abort(code: int) {
    $abort_flag := true;
    $abort_code := code;
}

function {:inline} $StdError(cat: int, reason: int): int {
    reason * 256 + cat
}

procedure {:inline 1} $InitVerification() {
    // Set abort_flag to false, and havoc abort_code
    $abort_flag := false;
    havoc $abort_code;
    // Initialize event store
    call $InitEventStore();
}

// ============================================================================================
// Instructions


procedure {:inline 1} $CastU8(src: int) returns (dst: int)
{
    if (src > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU64(src: int) returns (dst: int)
{
    if (src > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU128(src: int) returns (dst: int)
{
    if (src > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $AddU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU64(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU64_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU128(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU128_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $Sub(src1: int, src2: int) returns (dst: int)
{
    if (src1 < src2) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 - src2;
}

// uninterpreted function to return an undefined value.
function $undefined_int(): int;

// Recursive exponentiation function
// Undefined unless e >=0.  $pow(0,0) is also undefined.
function $pow(n: int, e: int): int {
    if n != 0 && e == 0 then 1
    else if e > 0 then n * $pow(n, e - 1)
    else $undefined_int()
}

function $shl(src1: int, p: int): int {
    src1 * $pow(2, p)
}

function $shr(src1: int, p: int): int {
    src1 div $pow(2, p)
}

// We need to know the size of the destination in order to drop bits
// that have been shifted left more than that, so we have $ShlU8/64/128
procedure {:inline 1} $ShlU8(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shl(src1, src2) mod 256;
}

procedure {:inline 1} $ShlU64(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shl(src1, src2) mod 18446744073709551616;
}

procedure {:inline 1} $ShlU128(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shl(src1, src2) mod 340282366920938463463374607431768211456;
}

// We don't need to know the size of destination, so no $ShrU8, etc.
procedure {:inline 1} $Shr(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shr(src1, src2);
}

procedure {:inline 1} $MulU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU64(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU128(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $Div(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 div src2;
}

procedure {:inline 1} $Mod(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 mod src2;
}

procedure {:inline 1} $ArithBinaryUnimplemented(src1: int, src2: int) returns (dst: int);

procedure {:inline 1} $Lt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 < src2;
}

procedure {:inline 1} $Gt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 > src2;
}

procedure {:inline 1} $Le(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 <= src2;
}

procedure {:inline 1} $Ge(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 >= src2;
}

procedure {:inline 1} $And(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 && src2;
}

procedure {:inline 1} $Or(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 || src2;
}

procedure {:inline 1} $Not(src: bool) returns (dst: bool)
{
    dst := !src;
}

// Pack and Unpack are auto-generated for each type T


// ==================================================================================
// Native Vector

function {:inline} $SliceVecByRange<T>(v: Vec T, r: $Range): Vec T {
    SliceVec(v, lb#$Range(r), ub#$Range(r))
}

// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `$2_object_ID`

// Not inlined. It appears faster this way.
function $IsEqual'vec'$2_object_ID''(v1: Vec ($2_object_ID), v2: Vec ($2_object_ID)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'$2_object_ID'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsValid'vec'$2_object_ID''(v: Vec ($2_object_ID)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'$2_object_ID'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'$2_object_ID'(v: Vec ($2_object_ID), e: $2_object_ID): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$2_object_ID'(ReadVec(v, i), e))
}

function $IndexOfVec'$2_object_ID'(v: Vec ($2_object_ID), e: $2_object_ID): int;
axiom (forall v: Vec ($2_object_ID), e: $2_object_ID:: {$IndexOfVec'$2_object_ID'(v, e)}
    (var i := $IndexOfVec'$2_object_ID'(v, e);
     if (!$ContainsVec'$2_object_ID'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$2_object_ID'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'$2_object_ID'(ReadVec(v, j), e))));


function {:inline} $RangeVec'$2_object_ID'(v: Vec ($2_object_ID)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'$2_object_ID'(): Vec ($2_object_ID) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'$2_object_ID'() returns (v: Vec ($2_object_ID)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'$2_object_ID'(): Vec ($2_object_ID) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'$2_object_ID'(v: Vec ($2_object_ID)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'$2_object_ID'(m: $Mutation (Vec ($2_object_ID)), val: $2_object_ID) returns (m': $Mutation (Vec ($2_object_ID))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'$2_object_ID'(v: Vec ($2_object_ID), val: $2_object_ID): Vec ($2_object_ID) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'$2_object_ID'(m: $Mutation (Vec ($2_object_ID))) returns (e: $2_object_ID, m': $Mutation (Vec ($2_object_ID))) {
    var v: Vec ($2_object_ID);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'$2_object_ID'(m: $Mutation (Vec ($2_object_ID)), other: Vec ($2_object_ID)) returns (m': $Mutation (Vec ($2_object_ID))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'$2_object_ID'(m: $Mutation (Vec ($2_object_ID))) returns (m': $Mutation (Vec ($2_object_ID))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_length'$2_object_ID'(v: Vec ($2_object_ID)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'$2_object_ID'(v: Vec ($2_object_ID)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'$2_object_ID'(v: Vec ($2_object_ID), i: int) returns (dst: $2_object_ID) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'$2_object_ID'(v: Vec ($2_object_ID), i: int): $2_object_ID {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'$2_object_ID'(m: $Mutation (Vec ($2_object_ID)), index: int)
returns (dst: $Mutation ($2_object_ID), m': $Mutation (Vec ($2_object_ID)))
{
    var v: Vec ($2_object_ID);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'$2_object_ID'(v: Vec ($2_object_ID), i: int): $2_object_ID {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'$2_object_ID'(v: Vec ($2_object_ID)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'$2_object_ID'(m: $Mutation (Vec ($2_object_ID)), i: int, j: int) returns (m': $Mutation (Vec ($2_object_ID)))
{
    var v: Vec ($2_object_ID);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'$2_object_ID'(v: Vec ($2_object_ID), i: int, j: int): Vec ($2_object_ID) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'$2_object_ID'(m: $Mutation (Vec ($2_object_ID)), i: int) returns (e: $2_object_ID, m': $Mutation (Vec ($2_object_ID)))
{
    var v: Vec ($2_object_ID);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'$2_object_ID'(m: $Mutation (Vec ($2_object_ID)), i: int) returns (e: $2_object_ID, m': $Mutation (Vec ($2_object_ID)))
{
    var len: int;
    var v: Vec ($2_object_ID);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'$2_object_ID'(v: Vec ($2_object_ID), e: $2_object_ID) returns (res: bool)  {
    res := $ContainsVec'$2_object_ID'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'$2_object_ID'(v: Vec ($2_object_ID), e: $2_object_ID) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'$2_object_ID'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `$2_vec_map_Entry'address_$0_market_ColData'`

// Not inlined. It appears faster this way.
function $IsEqual'vec'$2_vec_map_Entry'address_$0_market_ColData'''(v1: Vec ($2_vec_map_Entry'address_$0_market_ColData'), v2: Vec ($2_vec_map_Entry'address_$0_market_ColData')): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'$2_vec_map_Entry'address_$0_market_ColData''(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsValid'vec'$2_vec_map_Entry'address_$0_market_ColData'''(v: Vec ($2_vec_map_Entry'address_$0_market_ColData')): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'$2_vec_map_Entry'address_$0_market_ColData''(ReadVec(v, i)))
}


function {:inline} $ContainsVec'$2_vec_map_Entry'address_$0_market_ColData''(v: Vec ($2_vec_map_Entry'address_$0_market_ColData'), e: $2_vec_map_Entry'address_$0_market_ColData'): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$2_vec_map_Entry'address_$0_market_ColData''(ReadVec(v, i), e))
}

function $IndexOfVec'$2_vec_map_Entry'address_$0_market_ColData''(v: Vec ($2_vec_map_Entry'address_$0_market_ColData'), e: $2_vec_map_Entry'address_$0_market_ColData'): int;
axiom (forall v: Vec ($2_vec_map_Entry'address_$0_market_ColData'), e: $2_vec_map_Entry'address_$0_market_ColData':: {$IndexOfVec'$2_vec_map_Entry'address_$0_market_ColData''(v, e)}
    (var i := $IndexOfVec'$2_vec_map_Entry'address_$0_market_ColData''(v, e);
     if (!$ContainsVec'$2_vec_map_Entry'address_$0_market_ColData''(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'$2_vec_map_Entry'address_$0_market_ColData''(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'$2_vec_map_Entry'address_$0_market_ColData''(ReadVec(v, j), e))));


function {:inline} $RangeVec'$2_vec_map_Entry'address_$0_market_ColData''(v: Vec ($2_vec_map_Entry'address_$0_market_ColData')): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'$2_vec_map_Entry'address_$0_market_ColData''(): Vec ($2_vec_map_Entry'address_$0_market_ColData') {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'$2_vec_map_Entry'address_$0_market_ColData''() returns (v: Vec ($2_vec_map_Entry'address_$0_market_ColData')) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'$2_vec_map_Entry'address_$0_market_ColData''(): Vec ($2_vec_map_Entry'address_$0_market_ColData') {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'$2_vec_map_Entry'address_$0_market_ColData''(v: Vec ($2_vec_map_Entry'address_$0_market_ColData')) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'$2_vec_map_Entry'address_$0_market_ColData''(m: $Mutation (Vec ($2_vec_map_Entry'address_$0_market_ColData')), val: $2_vec_map_Entry'address_$0_market_ColData') returns (m': $Mutation (Vec ($2_vec_map_Entry'address_$0_market_ColData'))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'$2_vec_map_Entry'address_$0_market_ColData''(v: Vec ($2_vec_map_Entry'address_$0_market_ColData'), val: $2_vec_map_Entry'address_$0_market_ColData'): Vec ($2_vec_map_Entry'address_$0_market_ColData') {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'$2_vec_map_Entry'address_$0_market_ColData''(m: $Mutation (Vec ($2_vec_map_Entry'address_$0_market_ColData'))) returns (e: $2_vec_map_Entry'address_$0_market_ColData', m': $Mutation (Vec ($2_vec_map_Entry'address_$0_market_ColData'))) {
    var v: Vec ($2_vec_map_Entry'address_$0_market_ColData');
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'$2_vec_map_Entry'address_$0_market_ColData''(m: $Mutation (Vec ($2_vec_map_Entry'address_$0_market_ColData')), other: Vec ($2_vec_map_Entry'address_$0_market_ColData')) returns (m': $Mutation (Vec ($2_vec_map_Entry'address_$0_market_ColData'))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'$2_vec_map_Entry'address_$0_market_ColData''(m: $Mutation (Vec ($2_vec_map_Entry'address_$0_market_ColData'))) returns (m': $Mutation (Vec ($2_vec_map_Entry'address_$0_market_ColData'))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_length'$2_vec_map_Entry'address_$0_market_ColData''(v: Vec ($2_vec_map_Entry'address_$0_market_ColData')) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'$2_vec_map_Entry'address_$0_market_ColData''(v: Vec ($2_vec_map_Entry'address_$0_market_ColData')): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'$2_vec_map_Entry'address_$0_market_ColData''(v: Vec ($2_vec_map_Entry'address_$0_market_ColData'), i: int) returns (dst: $2_vec_map_Entry'address_$0_market_ColData') {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'$2_vec_map_Entry'address_$0_market_ColData''(v: Vec ($2_vec_map_Entry'address_$0_market_ColData'), i: int): $2_vec_map_Entry'address_$0_market_ColData' {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'$2_vec_map_Entry'address_$0_market_ColData''(m: $Mutation (Vec ($2_vec_map_Entry'address_$0_market_ColData')), index: int)
returns (dst: $Mutation ($2_vec_map_Entry'address_$0_market_ColData'), m': $Mutation (Vec ($2_vec_map_Entry'address_$0_market_ColData')))
{
    var v: Vec ($2_vec_map_Entry'address_$0_market_ColData');
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'$2_vec_map_Entry'address_$0_market_ColData''(v: Vec ($2_vec_map_Entry'address_$0_market_ColData'), i: int): $2_vec_map_Entry'address_$0_market_ColData' {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'$2_vec_map_Entry'address_$0_market_ColData''(v: Vec ($2_vec_map_Entry'address_$0_market_ColData')) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'$2_vec_map_Entry'address_$0_market_ColData''(m: $Mutation (Vec ($2_vec_map_Entry'address_$0_market_ColData')), i: int, j: int) returns (m': $Mutation (Vec ($2_vec_map_Entry'address_$0_market_ColData')))
{
    var v: Vec ($2_vec_map_Entry'address_$0_market_ColData');
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'$2_vec_map_Entry'address_$0_market_ColData''(v: Vec ($2_vec_map_Entry'address_$0_market_ColData'), i: int, j: int): Vec ($2_vec_map_Entry'address_$0_market_ColData') {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'$2_vec_map_Entry'address_$0_market_ColData''(m: $Mutation (Vec ($2_vec_map_Entry'address_$0_market_ColData')), i: int) returns (e: $2_vec_map_Entry'address_$0_market_ColData', m': $Mutation (Vec ($2_vec_map_Entry'address_$0_market_ColData')))
{
    var v: Vec ($2_vec_map_Entry'address_$0_market_ColData');

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'$2_vec_map_Entry'address_$0_market_ColData''(m: $Mutation (Vec ($2_vec_map_Entry'address_$0_market_ColData')), i: int) returns (e: $2_vec_map_Entry'address_$0_market_ColData', m': $Mutation (Vec ($2_vec_map_Entry'address_$0_market_ColData')))
{
    var len: int;
    var v: Vec ($2_vec_map_Entry'address_$0_market_ColData');

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'$2_vec_map_Entry'address_$0_market_ColData''(v: Vec ($2_vec_map_Entry'address_$0_market_ColData'), e: $2_vec_map_Entry'address_$0_market_ColData') returns (res: bool)  {
    res := $ContainsVec'$2_vec_map_Entry'address_$0_market_ColData''(v, e);
}

procedure {:inline 1}
$1_vector_index_of'$2_vec_map_Entry'address_$0_market_ColData''(v: Vec ($2_vec_map_Entry'address_$0_market_ColData'), e: $2_vec_map_Entry'address_$0_market_ColData') returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'$2_vec_map_Entry'address_$0_market_ColData''(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `address`

// Not inlined. It appears faster this way.
function $IsEqual'vec'address''(v1: Vec (int), v2: Vec (int)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'address'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsValid'vec'address''(v: Vec (int)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'address'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'address'(v: Vec (int), e: int): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'address'(ReadVec(v, i), e))
}

function $IndexOfVec'address'(v: Vec (int), e: int): int;
axiom (forall v: Vec (int), e: int:: {$IndexOfVec'address'(v, e)}
    (var i := $IndexOfVec'address'(v, e);
     if (!$ContainsVec'address'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'address'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'address'(ReadVec(v, j), e))));


function {:inline} $RangeVec'address'(v: Vec (int)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'address'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'address'() returns (v: Vec (int)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'address'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'address'(v: Vec (int)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'address'(m: $Mutation (Vec (int)), val: int) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'address'(v: Vec (int), val: int): Vec (int) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'address'(m: $Mutation (Vec (int))) returns (e: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'address'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'address'(m: $Mutation (Vec (int))) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_length'address'(v: Vec (int)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'address'(v: Vec (int)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'address'(v: Vec (int), i: int) returns (dst: int) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'address'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'address'(m: $Mutation (Vec (int)), index: int)
returns (dst: $Mutation (int), m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'address'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'address'(v: Vec (int)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'address'(m: $Mutation (Vec (int)), i: int, j: int) returns (m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'address'(v: Vec (int), i: int, j: int): Vec (int) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'address'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var v: Vec (int);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'address'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var len: int;
    var v: Vec (int);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'address'(v: Vec (int), e: int) returns (res: bool)  {
    res := $ContainsVec'address'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'address'(v: Vec (int), e: int) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'address'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `u64`

// Not inlined. It appears faster this way.
function $IsEqual'vec'u64''(v1: Vec (int), v2: Vec (int)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'u64'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsValid'vec'u64''(v: Vec (int)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'u64'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'u64'(v: Vec (int), e: int): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u64'(ReadVec(v, i), e))
}

function $IndexOfVec'u64'(v: Vec (int), e: int): int;
axiom (forall v: Vec (int), e: int:: {$IndexOfVec'u64'(v, e)}
    (var i := $IndexOfVec'u64'(v, e);
     if (!$ContainsVec'u64'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u64'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'u64'(ReadVec(v, j), e))));


function {:inline} $RangeVec'u64'(v: Vec (int)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'u64'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'u64'() returns (v: Vec (int)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'u64'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'u64'(v: Vec (int)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'u64'(m: $Mutation (Vec (int)), val: int) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'u64'(v: Vec (int), val: int): Vec (int) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'u64'(m: $Mutation (Vec (int))) returns (e: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'u64'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'u64'(m: $Mutation (Vec (int))) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_length'u64'(v: Vec (int)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'u64'(v: Vec (int)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'u64'(v: Vec (int), i: int) returns (dst: int) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'u64'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'u64'(m: $Mutation (Vec (int)), index: int)
returns (dst: $Mutation (int), m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'u64'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'u64'(v: Vec (int)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'u64'(m: $Mutation (Vec (int)), i: int, j: int) returns (m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'u64'(v: Vec (int), i: int, j: int): Vec (int) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'u64'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var v: Vec (int);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'u64'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var len: int;
    var v: Vec (int);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'u64'(v: Vec (int), e: int) returns (res: bool)  {
    res := $ContainsVec'u64'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'u64'(v: Vec (int), e: int) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'u64'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `u8`

// Not inlined. It appears faster this way.
function $IsEqual'vec'u8''(v1: Vec (int), v2: Vec (int)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'u8'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsValid'vec'u8''(v: Vec (int)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'u8'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'u8'(v: Vec (int), e: int): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u8'(ReadVec(v, i), e))
}

function $IndexOfVec'u8'(v: Vec (int), e: int): int;
axiom (forall v: Vec (int), e: int:: {$IndexOfVec'u8'(v, e)}
    (var i := $IndexOfVec'u8'(v, e);
     if (!$ContainsVec'u8'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u8'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'u8'(ReadVec(v, j), e))));


function {:inline} $RangeVec'u8'(v: Vec (int)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'u8'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'u8'() returns (v: Vec (int)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'u8'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'u8'(v: Vec (int)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'u8'(m: $Mutation (Vec (int)), val: int) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'u8'(v: Vec (int), val: int): Vec (int) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'u8'(m: $Mutation (Vec (int))) returns (e: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'u8'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'u8'(m: $Mutation (Vec (int))) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_length'u8'(v: Vec (int)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'u8'(v: Vec (int)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'u8'(v: Vec (int), i: int) returns (dst: int) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'u8'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'u8'(m: $Mutation (Vec (int)), index: int)
returns (dst: $Mutation (int), m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'u8'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'u8'(v: Vec (int)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'u8'(m: $Mutation (Vec (int)), i: int, j: int) returns (m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'u8'(v: Vec (int), i: int, j: int): Vec (int) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'u8'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var v: Vec (int);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_swap_remove'u8'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var len: int;
    var v: Vec (int);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'u8'(v: Vec (int), e: int) returns (res: bool)  {
    res := $ContainsVec'u8'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'u8'(v: Vec (int), e: int) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'u8'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ==================================================================================
// Native Table

// ==================================================================================
// Native Hash

// Hash is modeled as an otherwise uninterpreted injection.
// In truth, it is not an injection since the domain has greater cardinality
// (arbitrary length vectors) than the co-domain (vectors of length 32).  But it is
// common to assume in code there are no hash collisions in practice.  Fortunately,
// Boogie is not smart enough to recognized that there is an inconsistency.
// FIXME: If we were using a reliable extensional theory of arrays, and if we could use ==
// instead of $IsEqual, we might be able to avoid so many quantified formulas by
// using a sha2_inverse function in the ensures conditions of Hash_sha2_256 to
// assert that sha2/3 are injections without using global quantified axioms.


function $1_hash_sha2(val: Vec int): Vec int;

// This says that Hash_sha2 is bijective.
axiom (forall v1,v2: Vec int :: {$1_hash_sha2(v1), $1_hash_sha2(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_hash_sha2(v1), $1_hash_sha2(v2)));

procedure $1_hash_sha2_256(val: Vec int) returns (res: Vec int);
ensures res == $1_hash_sha2(val);     // returns Hash_sha2 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_hash_$sha2_256(val: Vec int): Vec int {
    $1_hash_sha2(val)
}

// similarly for Hash_sha3
function $1_hash_sha3(val: Vec int): Vec int;

axiom (forall v1,v2: Vec int :: {$1_hash_sha3(v1), $1_hash_sha3(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_hash_sha3(v1), $1_hash_sha3(v2)));

procedure $1_hash_sha3_256(val: Vec int) returns (res: Vec int);
ensures res == $1_hash_sha3(val);     // returns Hash_sha3 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_hash_$sha3_256(val: Vec int): Vec int {
    $1_hash_sha3(val)
}

// ==================================================================================
// Native string

// TODO: correct implementation of strings

procedure {:inline 1} $1_string_internal_check_utf8(x: Vec int) returns (r: bool) {
}

procedure {:inline 1} $1_string_internal_sub_string(x: Vec int, i: int, j: int) returns (r: Vec int) {
}

procedure {:inline 1} $1_string_internal_index_of(x: Vec int, y: Vec int) returns (r: int) {
}

procedure {:inline 1} $1_string_internal_is_char_boundary(x: Vec int, i: int) returns (r: bool) {
}




// ==================================================================================
// Native diem_account

procedure {:inline 1} $1_DiemAccount_create_signer(
  addr: int
) returns (signer: $signer) {
    // A signer is currently identical to an address.
    signer := $signer(addr);
}

procedure {:inline 1} $1_DiemAccount_destroy_signer(
  signer: $signer
) {
  return;
}

// ==================================================================================
// Native account

procedure {:inline 1} $1_Account_create_signer(
  addr: int
) returns (signer: $signer) {
    // A signer is currently identical to an address.
    signer := $signer(addr);
}

// ==================================================================================
// Native Signer

type {:datatype} $signer;
function {:constructor} $signer($addr: int): $signer;
function {:inline} $IsValid'signer'(s: $signer): bool {
    $IsValid'address'($addr#$signer(s))
}
function {:inline} $IsEqual'signer'(s1: $signer, s2: $signer): bool {
    s1 == s2
}

procedure {:inline 1} $1_signer_borrow_address(signer: $signer) returns (res: int) {
    res := $addr#$signer(signer);
}

function {:inline} $1_signer_$borrow_address(signer: $signer): int
{
    $addr#$signer(signer)
}

function $1_signer_is_txn_signer(s: $signer): bool;

function $1_signer_is_txn_signer_addr(a: int): bool;


// ==================================================================================
// Native signature

// Signature related functionality is handled via uninterpreted functions. This is sound
// currently because we verify every code path based on signature verification with
// an arbitrary interpretation.

function $1_Signature_$ed25519_validate_pubkey(public_key: Vec int): bool;
function $1_Signature_$ed25519_verify(signature: Vec int, public_key: Vec int, message: Vec int): bool;

// Needed because we do not have extensional equality:
axiom (forall k1, k2: Vec int ::
    {$1_Signature_$ed25519_validate_pubkey(k1), $1_Signature_$ed25519_validate_pubkey(k2)}
    $IsEqual'vec'u8''(k1, k2) ==> $1_Signature_$ed25519_validate_pubkey(k1) == $1_Signature_$ed25519_validate_pubkey(k2));
axiom (forall s1, s2, k1, k2, m1, m2: Vec int ::
    {$1_Signature_$ed25519_verify(s1, k1, m1), $1_Signature_$ed25519_verify(s2, k2, m2)}
    $IsEqual'vec'u8''(s1, s2) && $IsEqual'vec'u8''(k1, k2) && $IsEqual'vec'u8''(m1, m2)
    ==> $1_Signature_$ed25519_verify(s1, k1, m1) == $1_Signature_$ed25519_verify(s2, k2, m2));


procedure {:inline 1} $1_Signature_ed25519_validate_pubkey(public_key: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_validate_pubkey(public_key);
}

procedure {:inline 1} $1_Signature_ed25519_verify(
        signature: Vec int, public_key: Vec int, message: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_verify(signature, public_key, message);
}


// ==================================================================================
// Native bcs::serialize


// ==================================================================================
// Native Event module



procedure {:inline 1} $InitEventStore() {
}



//==================================
// Begin Translation



// Given Types for Type Parameters

type #0;
function {:inline} $IsEqual'#0'(x1: #0, x2: #0): bool { x1 == x2 }
function {:inline} $IsValid'#0'(x: #0): bool { true }
type #1;
function {:inline} $IsEqual'#1'(x1: #1, x2: #1): bool { x1 == x2 }
function {:inline} $IsValid'#1'(x: #1): bool { true }

// fun oracle::usd_value<#0> [baseline] at ./sources/oracle.move:4:5+72
procedure {:inline 1} $0_oracle_usd_value'#0'(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t0: int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[amount]($t0) at ./sources/oracle.move:4:5+1
    assume {:print "$at(64,144,145)"} true;
    assume {:print "$track_local(0,0,0):", $t0} $t0 == $t0;

    // trace_return[0]($t0) at ./sources/oracle.move:5:9+13
    assume {:print "$at(64,197,210)"} true;
    assume {:print "$track_return(0,0,0):", $t0} $t0 == $t0;

    // label L1 at ./sources/oracle.move:6:5+1
    assume {:print "$at(64,215,216)"} true;
L1:

    // return $t0 at ./sources/oracle.move:6:5+1
    $ret0 := $t0;
    return;

}

// fun oracle::usd_value<#1> [baseline] at ./sources/oracle.move:4:5+72
procedure {:inline 1} $0_oracle_usd_value'#1'(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t0: int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[amount]($t0) at ./sources/oracle.move:4:5+1
    assume {:print "$at(64,144,145)"} true;
    assume {:print "$track_local(0,0,0):", $t0} $t0 == $t0;

    // trace_return[0]($t0) at ./sources/oracle.move:5:9+13
    assume {:print "$at(64,197,210)"} true;
    assume {:print "$track_return(0,0,0):", $t0} $t0 == $t0;

    // label L1 at ./sources/oracle.move:6:5+1
    assume {:print "$at(64,215,216)"} true;
L1:

    // return $t0 at ./sources/oracle.move:6:5+1
    $ret0 := $t0;
    return;

}

// fun oracle::usd_value [verification] at ./sources/oracle.move:4:5+72
procedure {:timeLimit 40} $0_oracle_usd_value$verify(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t0: int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/oracle.move:4:5+1
    assume {:print "$at(64,144,145)"} true;
    assume $IsValid'u64'($t0);

    // trace_local[amount]($t0) at ./sources/oracle.move:4:5+1
    assume {:print "$track_local(0,0,0):", $t0} $t0 == $t0;

    // trace_return[0]($t0) at ./sources/oracle.move:5:9+13
    assume {:print "$at(64,197,210)"} true;
    assume {:print "$track_return(0,0,0):", $t0} $t0 == $t0;

    // label L1 at ./sources/oracle.move:6:5+1
    assume {:print "$at(64,215,216)"} true;
L1:

    // return $t0 at ./sources/oracle.move:6:5+1
    $ret0 := $t0;
    return;

}

// fun calculator::required_collateral_amount<#0, #1> [baseline] at ./sources/calculator.move:9:5+226
procedure {:inline 1} $0_calculator_required_collateral_amount'#0_#1'(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t0: int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[bor_amount]($t0) at ./sources/calculator.move:9:5+1
    assume {:print "$at(15,282,283)"} true;
    assume {:print "$track_local(1,0,0):", $t0} $t0 == $t0;

    // $t2 := oracle::usd_value<#0>($t0) on_abort goto L2 with $t3 at ./sources/calculator.move:10:38+32
    assume {:print "$at(15,388,420)"} true;
    call $t2 := $0_oracle_usd_value'#0'($t0);
    if ($abort_flag) {
        assume {:print "$at(15,388,420)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(1,0):", $t3} $t3 == $t3;
        goto L2;
    }

    // $t4 := 2 at ./sources/calculator.move:10:73+20
    $t4 := 2;
    assume $IsValid'u64'($t4);

    // $t5 := *($t2, $t4) on_abort goto L2 with $t3 at ./sources/calculator.move:10:71+1
    call $t5 := $MulU64($t2, $t4);
    if ($abort_flag) {
        assume {:print "$at(15,421,422)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(1,0):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_local[required_col_usd_value]($t5) at ./sources/calculator.move:10:13+22
    assume {:print "$track_local(1,0,1):", $t5} $t5 == $t5;

    // $t6 := 1 at ./sources/calculator.move:12:55+1
    assume {:print "$at(15,500,501)"} true;
    $t6 := 1;
    assume $IsValid'u64'($t6);

    // $t7 := oracle::usd_value<#1>($t6) on_abort goto L2 with $t3 at ./sources/calculator.move:12:34+23
    call $t7 := $0_oracle_usd_value'#1'($t6);
    if ($abort_flag) {
        assume {:print "$at(15,479,502)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(1,0):", $t3} $t3 == $t3;
        goto L2;
    }

    // $t8 := /($t5, $t7) on_abort goto L2 with $t3 at ./sources/calculator.move:12:32+1
    call $t8 := $Div($t5, $t7);
    if ($abort_flag) {
        assume {:print "$at(15,477,478)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(1,0):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_return[0]($t8) at ./sources/calculator.move:12:9+48
    assume {:print "$track_return(1,0,0):", $t8} $t8 == $t8;

    // label L1 at ./sources/calculator.move:13:5+1
    assume {:print "$at(15,507,508)"} true;
L1:

    // return $t8 at ./sources/calculator.move:13:5+1
    $ret0 := $t8;
    return;

    // label L2 at ./sources/calculator.move:13:5+1
L2:

    // abort($t3) at ./sources/calculator.move:13:5+1
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun calculator::required_collateral_amount [verification] at ./sources/calculator.move:9:5+226
procedure {:timeLimit 40} $0_calculator_required_collateral_amount$verify(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t0: int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/calculator.move:9:5+1
    assume {:print "$at(15,282,283)"} true;
    assume $IsValid'u64'($t0);

    // trace_local[bor_amount]($t0) at ./sources/calculator.move:9:5+1
    assume {:print "$track_local(1,0,0):", $t0} $t0 == $t0;

    // $t2 := oracle::usd_value<#0>($t0) on_abort goto L2 with $t3 at ./sources/calculator.move:10:38+32
    assume {:print "$at(15,388,420)"} true;
    call $t2 := $0_oracle_usd_value'#0'($t0);
    if ($abort_flag) {
        assume {:print "$at(15,388,420)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(1,0):", $t3} $t3 == $t3;
        goto L2;
    }

    // $t4 := 2 at ./sources/calculator.move:10:73+20
    $t4 := 2;
    assume $IsValid'u64'($t4);

    // $t5 := *($t2, $t4) on_abort goto L2 with $t3 at ./sources/calculator.move:10:71+1
    call $t5 := $MulU64($t2, $t4);
    if ($abort_flag) {
        assume {:print "$at(15,421,422)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(1,0):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_local[required_col_usd_value]($t5) at ./sources/calculator.move:10:13+22
    assume {:print "$track_local(1,0,1):", $t5} $t5 == $t5;

    // $t6 := 1 at ./sources/calculator.move:12:55+1
    assume {:print "$at(15,500,501)"} true;
    $t6 := 1;
    assume $IsValid'u64'($t6);

    // $t7 := oracle::usd_value<#1>($t6) on_abort goto L2 with $t3 at ./sources/calculator.move:12:34+23
    call $t7 := $0_oracle_usd_value'#1'($t6);
    if ($abort_flag) {
        assume {:print "$at(15,479,502)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(1,0):", $t3} $t3 == $t3;
        goto L2;
    }

    // $t8 := /($t5, $t7) on_abort goto L2 with $t3 at ./sources/calculator.move:12:32+1
    call $t8 := $Div($t5, $t7);
    if ($abort_flag) {
        assume {:print "$at(15,477,478)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(1,0):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_return[0]($t8) at ./sources/calculator.move:12:9+48
    assume {:print "$track_return(1,0,0):", $t8} $t8 == $t8;

    // label L1 at ./sources/calculator.move:13:5+1
    assume {:print "$at(15,507,508)"} true;
L1:

    // return $t8 at ./sources/calculator.move:13:5+1
    $ret0 := $t8;
    return;

    // label L2 at ./sources/calculator.move:13:5+1
L2:

    // abort($t3) at ./sources/calculator.move:13:5+1
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// spec fun at ./../sui/crates/sui-framework/deps/move-stdlib/sources/vector.move:102:5+86
function {:inline} $1_vector_$is_empty'u64'(v: Vec (int)): bool {
    $IsEqual'u64'($1_vector_$length'u64'(v), 0)
}

// spec fun at ./../sui/crates/sui-framework/deps/move-stdlib/sources/option.move:89:5+171
function {:inline} $1_option_$borrow'u64'(t: $1_option_Option'u64'): int {
    $1_vector_$borrow'u64'($vec#$1_option_Option'u64'(t), 0)
}

// spec fun at ./../sui/crates/sui-framework/deps/move-stdlib/sources/option.move:54:5+95
function {:inline} $1_option_$is_none'u64'(t: $1_option_Option'u64'): bool {
    $1_vector_$is_empty'u64'($vec#$1_option_Option'u64'(t))
}

// spec fun at ./../sui/crates/sui-framework/deps/move-stdlib/sources/option.move:64:5+96
function {:inline} $1_option_$is_some'u64'(t: $1_option_Option'u64'): bool {
    !$1_vector_$is_empty'u64'($vec#$1_option_Option'u64'(t))
}

// spec fun at ./../sui/crates/sui-framework/deps/move-stdlib/sources/option.move:36:10+78
function {:inline} $1_option_spec_none'u64'(): $1_option_Option'u64' {
    $1_option_Option'u64'($EmptyVec'u64'())
}

// spec fun at ./../sui/crates/sui-framework/deps/move-stdlib/sources/option.move:49:10+89
function {:inline} $1_option_spec_some'u64'(e: int): $1_option_Option'u64' {
    $1_option_Option'u64'(MakeVec1(e))
}

// struct option::Option<u64> at ./../sui/crates/sui-framework/deps/move-stdlib/sources/option.move:11:5+81
type {:datatype} $1_option_Option'u64';
function {:constructor} $1_option_Option'u64'($vec: Vec (int)): $1_option_Option'u64';
function {:inline} $Update'$1_option_Option'u64''_vec(s: $1_option_Option'u64', x: Vec (int)): $1_option_Option'u64' {
    $1_option_Option'u64'(x)
}
function $IsValid'$1_option_Option'u64''(s: $1_option_Option'u64'): bool {
    $IsValid'vec'u64''($vec#$1_option_Option'u64'(s))
}
function {:inline} $IsEqual'$1_option_Option'u64''(s1: $1_option_Option'u64', s2: $1_option_Option'u64'): bool {
    $IsEqual'vec'u64''($vec#$1_option_Option'u64'(s1), $vec#$1_option_Option'u64'(s2))}

// struct vec_set::VecSet<object::ID> at ./../sui/crates/sui-framework/sources/vec_set.move:18:5+88
type {:datatype} $2_vec_set_VecSet'$2_object_ID';
function {:constructor} $2_vec_set_VecSet'$2_object_ID'($contents: Vec ($2_object_ID)): $2_vec_set_VecSet'$2_object_ID';
function {:inline} $Update'$2_vec_set_VecSet'$2_object_ID''_contents(s: $2_vec_set_VecSet'$2_object_ID', x: Vec ($2_object_ID)): $2_vec_set_VecSet'$2_object_ID' {
    $2_vec_set_VecSet'$2_object_ID'(x)
}
function $IsValid'$2_vec_set_VecSet'$2_object_ID''(s: $2_vec_set_VecSet'$2_object_ID'): bool {
    $IsValid'vec'$2_object_ID''($contents#$2_vec_set_VecSet'$2_object_ID'(s))
}
function {:inline} $IsEqual'$2_vec_set_VecSet'$2_object_ID''(s1: $2_vec_set_VecSet'$2_object_ID', s2: $2_vec_set_VecSet'$2_object_ID'): bool {
    $IsEqual'vec'$2_object_ID''($contents#$2_vec_set_VecSet'$2_object_ID'(s1), $contents#$2_vec_set_VecSet'$2_object_ID'(s2))}

// fun vec_set::contains<object::ID> [baseline] at ./../sui/crates/sui-framework/sources/vec_set.move:41:5+125
procedure {:inline 1} $2_vec_set_contains'$2_object_ID'(_$t0: $2_vec_set_VecSet'$2_object_ID', _$t1: $2_object_ID) returns ($ret0: bool)
{
    // declare local variables
    var $t2: $1_option_Option'u64';
    var $t3: $1_option_Option'u64';
    var $t4: int;
    var $t5: bool;
    var $t0: $2_vec_set_VecSet'$2_object_ID';
    var $t1: $2_object_ID;
    var $temp_0'$2_object_ID': $2_object_ID;
    var $temp_0'$2_vec_set_VecSet'$2_object_ID'': $2_vec_set_VecSet'$2_object_ID';
    var $temp_0'bool': bool;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../sui/crates/sui-framework/sources/vec_set.move:41:5+1
    assume {:print "$at(37,1532,1533)"} true;
    assume {:print "$track_local(5,0,0):", $t0} $t0 == $t0;

    // trace_local[key]($t1) at ./../sui/crates/sui-framework/sources/vec_set.move:41:5+1
    assume {:print "$track_local(5,0,1):", $t1} $t1 == $t1;

    // $t3 := vec_set::get_idx_opt<#0>($t0, $t1) on_abort goto L2 with $t4 at ./../sui/crates/sui-framework/sources/vec_set.move:42:26+22
    assume {:print "$at(37,1628,1650)"} true;
    call $t3 := $2_vec_set_get_idx_opt'$2_object_ID'($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(37,1628,1650)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(5,0):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t5 := opaque begin: option::is_some<u64>($t3) at ./../sui/crates/sui-framework/sources/vec_set.move:42:9+40

    // assume WellFormed($t5) at ./../sui/crates/sui-framework/sources/vec_set.move:42:9+40
    assume $IsValid'bool'($t5);

    // assume Eq<bool>($t5, option::$is_some<u64>($t3)) at ./../sui/crates/sui-framework/sources/vec_set.move:42:9+40
    assume $IsEqual'bool'($t5, $1_option_$is_some'u64'($t3));

    // $t5 := opaque end: option::is_some<u64>($t3) at ./../sui/crates/sui-framework/sources/vec_set.move:42:9+40

    // trace_return[0]($t5) at ./../sui/crates/sui-framework/sources/vec_set.move:42:9+40
    assume {:print "$track_return(5,0,0):", $t5} $t5 == $t5;

    // label L1 at ./../sui/crates/sui-framework/sources/vec_set.move:43:5+1
    assume {:print "$at(37,1656,1657)"} true;
L1:

    // return $t5 at ./../sui/crates/sui-framework/sources/vec_set.move:43:5+1
    $ret0 := $t5;
    return;

    // label L2 at ./../sui/crates/sui-framework/sources/vec_set.move:43:5+1
L2:

    // abort($t4) at ./../sui/crates/sui-framework/sources/vec_set.move:43:5+1
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun vec_set::empty<object::ID> [baseline] at ./../sui/crates/sui-framework/sources/vec_set.move:23:5+98
procedure {:inline 1} $2_vec_set_empty'$2_object_ID'() returns ($ret0: $2_vec_set_VecSet'$2_object_ID')
{
    // declare local variables
    var $t0: Vec ($2_object_ID);
    var $t1: int;
    var $t2: $2_vec_set_VecSet'$2_object_ID';
    var $temp_0'$2_vec_set_VecSet'$2_object_ID'': $2_vec_set_VecSet'$2_object_ID';

    // bytecode translation starts here
    // $t0 := vector::empty<#0>() on_abort goto L2 with $t1 at ./../sui/crates/sui-framework/sources/vec_set.move:24:28+15
    assume {:print "$at(37,904,919)"} true;
    call $t0 := $1_vector_empty'$2_object_ID'();
    if ($abort_flag) {
        assume {:print "$at(37,904,919)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(5,1):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t2 := pack vec_set::VecSet<#0>($t0) at ./../sui/crates/sui-framework/sources/vec_set.move:24:9+36
    $t2 := $2_vec_set_VecSet'$2_object_ID'($t0);

    // trace_return[0]($t2) at ./../sui/crates/sui-framework/sources/vec_set.move:24:9+36
    assume {:print "$track_return(5,1,0):", $t2} $t2 == $t2;

    // label L1 at ./../sui/crates/sui-framework/sources/vec_set.move:25:5+1
    assume {:print "$at(37,926,927)"} true;
L1:

    // return $t2 at ./../sui/crates/sui-framework/sources/vec_set.move:25:5+1
    $ret0 := $t2;
    return;

    // label L2 at ./../sui/crates/sui-framework/sources/vec_set.move:25:5+1
L2:

    // abort($t1) at ./../sui/crates/sui-framework/sources/vec_set.move:25:5+1
    $abort_code := $t1;
    $abort_flag := true;
    return;

}

// fun vec_set::get_idx_opt<object::ID> [baseline] at ./../sui/crates/sui-framework/sources/vec_set.move:66:5+321
procedure {:inline 1} $2_vec_set_get_idx_opt'$2_object_ID'(_$t0: $2_vec_set_VecSet'$2_object_ID', _$t1: $2_object_ID) returns ($ret0: $1_option_Option'u64')
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: bool;
    var $t8: Vec ($2_object_ID);
    var $t9: $2_object_ID;
    var $t10: bool;
    var $t11: int;
    var $t12: int;
    var $t13: $1_option_Option'u64';
    var $t14: $1_option_Option'u64';
    var $t15: $1_option_Option'u64';
    var $t0: $2_vec_set_VecSet'$2_object_ID';
    var $t1: $2_object_ID;
    var $temp_0'$1_option_Option'u64'': $1_option_Option'u64';
    var $temp_0'$2_object_ID': $2_object_ID;
    var $temp_0'$2_vec_set_VecSet'$2_object_ID'': $2_vec_set_VecSet'$2_object_ID';
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../sui/crates/sui-framework/sources/vec_set.move:66:5+1
    assume {:print "$at(37,2406,2407)"} true;
    assume {:print "$track_local(5,3,0):", $t0} $t0 == $t0;

    // trace_local[key]($t1) at ./../sui/crates/sui-framework/sources/vec_set.move:66:5+1
    assume {:print "$track_local(5,3,1):", $t1} $t1 == $t1;

    // $t4 := 0 at ./../sui/crates/sui-framework/sources/vec_set.move:67:17+1
    assume {:print "$at(37,2496,2497)"} true;
    $t4 := 0;
    assume $IsValid'u64'($t4);

    // trace_local[i]($t4) at ./../sui/crates/sui-framework/sources/vec_set.move:67:13+1
    assume {:print "$track_local(5,3,2):", $t4} $t4 == $t4;

    // $t5 := vec_set::size<#0>($t0) on_abort goto L9 with $t6 at ./../sui/crates/sui-framework/sources/vec_set.move:68:17+10
    assume {:print "$at(37,2515,2525)"} true;
    call $t5 := $2_vec_set_size'$2_object_ID'($t0);
    if ($abort_flag) {
        assume {:print "$at(37,2515,2525)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(5,3):", $t6} $t6 == $t6;
        goto L9;
    }

    // trace_local[n]($t5) at ./../sui/crates/sui-framework/sources/vec_set.move:68:13+1
    assume {:print "$track_local(5,3,3):", $t5} $t5 == $t5;

    // label L6 at ./../sui/crates/sui-framework/sources/vec_set.move:69:16+1
    assume {:print "$at(37,2542,2543)"} true;
L6:

    // havoc[val]($t4) at ./../sui/crates/sui-framework/sources/vec_set.move:69:16+1
    havoc $t4;
    assume $IsValid'u64'($t4);

    // havoc[val]($t7) at ./../sui/crates/sui-framework/sources/vec_set.move:69:16+1
    havoc $t7;
    assume $IsValid'bool'($t7);

    // havoc[val]($t8) at ./../sui/crates/sui-framework/sources/vec_set.move:69:16+1
    havoc $t8;
    assume $IsValid'vec'$2_object_ID''($t8);

    // havoc[val]($t9) at ./../sui/crates/sui-framework/sources/vec_set.move:69:16+1
    havoc $t9;
    assume $IsValid'$2_object_ID'($t9);

    // havoc[val]($t10) at ./../sui/crates/sui-framework/sources/vec_set.move:69:16+1
    havoc $t10;
    assume $IsValid'bool'($t10);

    // havoc[val]($t11) at ./../sui/crates/sui-framework/sources/vec_set.move:69:16+1
    havoc $t11;
    assume $IsValid'u64'($t11);

    // havoc[val]($t12) at ./../sui/crates/sui-framework/sources/vec_set.move:69:16+1
    havoc $t12;
    assume $IsValid'u64'($t12);

    // trace_local[i]($t4) at ./../sui/crates/sui-framework/sources/vec_set.move:69:16+1
    assume {:print "$info(): enter loop, variable(s) i havocked and reassigned"} true;
    assume {:print "$track_local(5,3,2):", $t4} $t4 == $t4;

    // assume Not(AbortFlag()) at ./../sui/crates/sui-framework/sources/vec_set.move:69:16+1
    assume !$abort_flag;

    // $t7 := <($t4, $t5) at ./../sui/crates/sui-framework/sources/vec_set.move:69:18+1
    call $t7 := $Lt($t4, $t5);

    // if ($t7) goto L0 else goto L2 at ./../sui/crates/sui-framework/sources/vec_set.move:69:9+162
    if ($t7) { goto L0; } else { goto L2; }

    // label L0 at ./../sui/crates/sui-framework/sources/vec_set.move:70:33+4
    assume {:print "$at(37,2583,2587)"} true;
L0:

    // $t8 := get_field<vec_set::VecSet<#0>>.contents($t0) at ./../sui/crates/sui-framework/sources/vec_set.move:70:32+14
    $t8 := $contents#$2_vec_set_VecSet'$2_object_ID'($t0);

    // $t9 := vector::borrow<#0>($t8, $t4) on_abort goto L9 with $t6 at ./../sui/crates/sui-framework/sources/vec_set.move:70:17+33
    call $t9 := $1_vector_borrow'$2_object_ID'($t8, $t4);
    if ($abort_flag) {
        assume {:print "$at(37,2567,2600)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(5,3):", $t6} $t6 == $t6;
        goto L9;
    }

    // $t10 := ==($t9, $t1) at ./../sui/crates/sui-framework/sources/vec_set.move:70:51+2
    $t10 := $IsEqual'$2_object_ID'($t9, $t1);

    // if ($t10) goto L3 else goto L5 at ./../sui/crates/sui-framework/sources/vec_set.move:70:13+100
    if ($t10) { goto L3; } else { goto L5; }

    // label L3 at ./../sui/crates/sui-framework/sources/vec_set.move:71:17+22
    assume {:print "$at(37,2627,2649)"} true;
L3:

    // destroy($t0) at ./../sui/crates/sui-framework/sources/vec_set.move:71:17+22

    // destroy($t1) at ./../sui/crates/sui-framework/sources/vec_set.move:71:17+22

    // $t13 := opaque begin: option::some<u64>($t4) at ./../sui/crates/sui-framework/sources/vec_set.move:71:24+15

    // assume And(WellFormed($t13), Le(Len<u64>(select option::Option.vec($t13)), 1)) at ./../sui/crates/sui-framework/sources/vec_set.move:71:24+15
    assume ($IsValid'$1_option_Option'u64''($t13) && (LenVec($vec#$1_option_Option'u64'($t13)) <= 1));

    // assume Eq<option::Option<u64>>($t13, option::spec_some<u64>($t4)) at ./../sui/crates/sui-framework/sources/vec_set.move:71:24+15
    assume $IsEqual'$1_option_Option'u64''($t13, $1_option_spec_some'u64'($t4));

    // $t13 := opaque end: option::some<u64>($t4) at ./../sui/crates/sui-framework/sources/vec_set.move:71:24+15

    // trace_return[0]($t13) at ./../sui/crates/sui-framework/sources/vec_set.move:71:17+22
    assume {:print "$track_return(5,3,0):", $t13} $t13 == $t13;

    // $t14 := move($t13) at ./../sui/crates/sui-framework/sources/vec_set.move:71:17+22
    $t14 := $t13;

    // goto L8 at ./../sui/crates/sui-framework/sources/vec_set.move:71:17+22
    goto L8;

    // label L5 at ./../sui/crates/sui-framework/sources/vec_set.move:73:17+1
    assume {:print "$at(37,2681,2682)"} true;
L5:

    // $t11 := 1 at ./../sui/crates/sui-framework/sources/vec_set.move:73:21+1
    $t11 := 1;
    assume $IsValid'u64'($t11);

    // $t12 := +($t4, $t11) on_abort goto L9 with $t6 at ./../sui/crates/sui-framework/sources/vec_set.move:73:19+1
    call $t12 := $AddU64($t4, $t11);
    if ($abort_flag) {
        assume {:print "$at(37,2683,2684)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(5,3):", $t6} $t6 == $t6;
        goto L9;
    }

    // trace_local[i]($t12) at ./../sui/crates/sui-framework/sources/vec_set.move:73:13+1
    assume {:print "$track_local(5,3,2):", $t12} $t12 == $t12;

    // goto L7 at ./../sui/crates/sui-framework/sources/vec_set.move:73:22+1
    goto L7;

    // label L2 at ./../sui/crates/sui-framework/sources/vec_set.move:75:9+14
    assume {:print "$at(37,2707,2721)"} true;
L2:

    // destroy($t0) at ./../sui/crates/sui-framework/sources/vec_set.move:75:9+14

    // destroy($t1) at ./../sui/crates/sui-framework/sources/vec_set.move:75:9+14

    // $t15 := opaque begin: option::none<u64>() at ./../sui/crates/sui-framework/sources/vec_set.move:75:9+14

    // assume And(WellFormed($t15), Le(Len<u64>(select option::Option.vec($t15)), 1)) at ./../sui/crates/sui-framework/sources/vec_set.move:75:9+14
    assume ($IsValid'$1_option_Option'u64''($t15) && (LenVec($vec#$1_option_Option'u64'($t15)) <= 1));

    // assume Eq<option::Option<u64>>($t15, option::spec_none<u64>()) at ./../sui/crates/sui-framework/sources/vec_set.move:75:9+14
    assume $IsEqual'$1_option_Option'u64''($t15, $1_option_spec_none'u64'());

    // $t15 := opaque end: option::none<u64>() at ./../sui/crates/sui-framework/sources/vec_set.move:75:9+14

    // trace_return[0]($t15) at ./../sui/crates/sui-framework/sources/vec_set.move:75:9+14
    assume {:print "$track_return(5,3,0):", $t15} $t15 == $t15;

    // $t14 := move($t15) at ./../sui/crates/sui-framework/sources/vec_set.move:75:9+14
    $t14 := $t15;

    // goto L8 at ./../sui/crates/sui-framework/sources/vec_set.move:75:9+14
    goto L8;

    // label L7 at ./../sui/crates/sui-framework/sources/vec_set.move:75:9+14
    // Loop invariant checking block for the loop started with header: L6
L7:

    // stop() at ./../sui/crates/sui-framework/sources/vec_set.move:75:9+14
    assume false;
    return;

    // label L8 at ./../sui/crates/sui-framework/sources/vec_set.move:76:5+1
    assume {:print "$at(37,2726,2727)"} true;
L8:

    // return $t14 at ./../sui/crates/sui-framework/sources/vec_set.move:76:5+1
    $ret0 := $t14;
    return;

    // label L9 at ./../sui/crates/sui-framework/sources/vec_set.move:76:5+1
L9:

    // abort($t6) at ./../sui/crates/sui-framework/sources/vec_set.move:76:5+1
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun vec_set::insert<object::ID> [baseline] at ./../sui/crates/sui-framework/sources/vec_set.move:29:5+181
procedure {:inline 1} $2_vec_set_insert'$2_object_ID'(_$t0: $Mutation ($2_vec_set_VecSet'$2_object_ID'), _$t1: $2_object_ID) returns ($ret0: $Mutation ($2_vec_set_VecSet'$2_object_ID'))
{
    // declare local variables
    var $t2: $Mutation ($2_vec_set_VecSet'$2_object_ID');
    var $t3: $2_object_ID;
    var $t4: $2_vec_set_VecSet'$2_object_ID';
    var $t5: bool;
    var $t6: int;
    var $t7: bool;
    var $t8: int;
    var $t9: $Mutation (Vec ($2_object_ID));
    var $t0: $Mutation ($2_vec_set_VecSet'$2_object_ID');
    var $t1: $2_object_ID;
    var $temp_0'$2_object_ID': $2_object_ID;
    var $temp_0'$2_vec_set_VecSet'$2_object_ID'': $2_vec_set_VecSet'$2_object_ID';
    $t0 := _$t0;
    $t1 := _$t1;
    assume IsEmptyVec(p#$Mutation($t2));
    assume IsEmptyVec(p#$Mutation($t9));

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../sui/crates/sui-framework/sources/vec_set.move:29:5+1
    assume {:print "$at(37,1021,1022)"} true;
    $temp_0'$2_vec_set_VecSet'$2_object_ID'' := $Dereference($t0);
    assume {:print "$track_local(5,4,0):", $temp_0'$2_vec_set_VecSet'$2_object_ID''} $temp_0'$2_vec_set_VecSet'$2_object_ID'' == $temp_0'$2_vec_set_VecSet'$2_object_ID'';

    // trace_local[key]($t1) at ./../sui/crates/sui-framework/sources/vec_set.move:29:5+1
    assume {:print "$track_local(5,4,1):", $t1} $t1 == $t1;

    // $t4 := read_ref($t0) at ./../sui/crates/sui-framework/sources/vec_set.move:30:26+12
    assume {:print "$at(37,1112,1124)"} true;
    $t4 := $Dereference($t0);

    // $t5 := vec_set::contains<#0>($t4, $t1) on_abort goto L3 with $t6 at ./../sui/crates/sui-framework/sources/vec_set.move:30:18+20
    call $t5 := $2_vec_set_contains'$2_object_ID'($t4, $t1);
    if ($abort_flag) {
        assume {:print "$at(37,1104,1124)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(5,4):", $t6} $t6 == $t6;
        goto L3;
    }

    // $t7 := !($t5) at ./../sui/crates/sui-framework/sources/vec_set.move:30:17+1
    call $t7 := $Not($t5);

    // if ($t7) goto L0 else goto L1 at ./../sui/crates/sui-framework/sources/vec_set.move:30:9+49
    if ($t7) { goto L0; } else { goto L1; }

    // label L1 at ./../sui/crates/sui-framework/sources/vec_set.move:30:9+49
L1:

    // destroy($t0) at ./../sui/crates/sui-framework/sources/vec_set.move:30:9+49

    // $t8 := 0 at ./../sui/crates/sui-framework/sources/vec_set.move:30:40+17
    $t8 := 0;
    assume $IsValid'u64'($t8);

    // trace_abort($t8) at ./../sui/crates/sui-framework/sources/vec_set.move:30:9+49
    assume {:print "$at(37,1095,1144)"} true;
    assume {:print "$track_abort(5,4):", $t8} $t8 == $t8;

    // $t6 := move($t8) at ./../sui/crates/sui-framework/sources/vec_set.move:30:9+49
    $t6 := $t8;

    // goto L3 at ./../sui/crates/sui-framework/sources/vec_set.move:30:9+49
    goto L3;

    // label L0 at ./../sui/crates/sui-framework/sources/vec_set.move:31:32+4
    assume {:print "$at(37,1177,1181)"} true;
L0:

    // $t9 := borrow_field<vec_set::VecSet<#0>>.contents($t0) at ./../sui/crates/sui-framework/sources/vec_set.move:31:27+18
    $t9 := $ChildMutation($t0, 0, $contents#$2_vec_set_VecSet'$2_object_ID'($Dereference($t0)));

    // vector::push_back<#0>($t9, $t1) on_abort goto L3 with $t6 at ./../sui/crates/sui-framework/sources/vec_set.move:31:9+42
    call $t9 := $1_vector_push_back'$2_object_ID'($t9, $t1);
    if ($abort_flag) {
        assume {:print "$at(37,1154,1196)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(5,4):", $t6} $t6 == $t6;
        goto L3;
    }

    // write_back[Reference($t0).contents (vector<#0>)]($t9) at ./../sui/crates/sui-framework/sources/vec_set.move:31:9+42
    $t0 := $UpdateMutation($t0, $Update'$2_vec_set_VecSet'$2_object_ID''_contents($Dereference($t0), $Dereference($t9)));

    // trace_local[self]($t0) at ./../sui/crates/sui-framework/sources/vec_set.move:31:9+42
    $temp_0'$2_vec_set_VecSet'$2_object_ID'' := $Dereference($t0);
    assume {:print "$track_local(5,4,0):", $temp_0'$2_vec_set_VecSet'$2_object_ID''} $temp_0'$2_vec_set_VecSet'$2_object_ID'' == $temp_0'$2_vec_set_VecSet'$2_object_ID'';

    // trace_local[self]($t0) at ./../sui/crates/sui-framework/sources/vec_set.move:31:9+42
    $temp_0'$2_vec_set_VecSet'$2_object_ID'' := $Dereference($t0);
    assume {:print "$track_local(5,4,0):", $temp_0'$2_vec_set_VecSet'$2_object_ID''} $temp_0'$2_vec_set_VecSet'$2_object_ID'' == $temp_0'$2_vec_set_VecSet'$2_object_ID'';

    // label L2 at ./../sui/crates/sui-framework/sources/vec_set.move:32:5+1
    assume {:print "$at(37,1201,1202)"} true;
L2:

    // return () at ./../sui/crates/sui-framework/sources/vec_set.move:32:5+1
    $ret0 := $t0;
    return;

    // label L3 at ./../sui/crates/sui-framework/sources/vec_set.move:32:5+1
L3:

    // abort($t6) at ./../sui/crates/sui-framework/sources/vec_set.move:32:5+1
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun vec_set::size<object::ID> [baseline] at ./../sui/crates/sui-framework/sources/vec_set.move:46:5+101
procedure {:inline 1} $2_vec_set_size'$2_object_ID'(_$t0: $2_vec_set_VecSet'$2_object_ID') returns ($ret0: int)
{
    // declare local variables
    var $t1: Vec ($2_object_ID);
    var $t2: int;
    var $t3: int;
    var $t0: $2_vec_set_VecSet'$2_object_ID';
    var $temp_0'$2_vec_set_VecSet'$2_object_ID'': $2_vec_set_VecSet'$2_object_ID';
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../sui/crates/sui-framework/sources/vec_set.move:46:5+1
    assume {:print "$at(37,1710,1711)"} true;
    assume {:print "$track_local(5,8,0):", $t0} $t0 == $t0;

    // $t1 := get_field<vec_set::VecSet<#0>>.contents($t0) at ./../sui/crates/sui-framework/sources/vec_set.move:47:24+14
    assume {:print "$at(37,1790,1804)"} true;
    $t1 := $contents#$2_vec_set_VecSet'$2_object_ID'($t0);

    // $t2 := vector::length<#0>($t1) on_abort goto L2 with $t3 at ./../sui/crates/sui-framework/sources/vec_set.move:47:9+30
    call $t2 := $1_vector_length'$2_object_ID'($t1);
    if ($abort_flag) {
        assume {:print "$at(37,1775,1805)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(5,8):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_return[0]($t2) at ./../sui/crates/sui-framework/sources/vec_set.move:47:9+30
    assume {:print "$track_return(5,8,0):", $t2} $t2 == $t2;

    // label L1 at ./../sui/crates/sui-framework/sources/vec_set.move:48:5+1
    assume {:print "$at(37,1810,1811)"} true;
L1:

    // return $t2 at ./../sui/crates/sui-framework/sources/vec_set.move:48:5+1
    $ret0 := $t2;
    return;

    // label L2 at ./../sui/crates/sui-framework/sources/vec_set.move:48:5+1
L2:

    // abort($t3) at ./../sui/crates/sui-framework/sources/vec_set.move:48:5+1
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// struct vec_map::Entry<address, market::ColData> at ./../sui/crates/sui-framework/sources/vec_map.move:31:5+88
type {:datatype} $2_vec_map_Entry'address_$0_market_ColData';
function {:constructor} $2_vec_map_Entry'address_$0_market_ColData'($key: int, $value: $0_market_ColData): $2_vec_map_Entry'address_$0_market_ColData';
function {:inline} $Update'$2_vec_map_Entry'address_$0_market_ColData''_key(s: $2_vec_map_Entry'address_$0_market_ColData', x: int): $2_vec_map_Entry'address_$0_market_ColData' {
    $2_vec_map_Entry'address_$0_market_ColData'(x, $value#$2_vec_map_Entry'address_$0_market_ColData'(s))
}
function {:inline} $Update'$2_vec_map_Entry'address_$0_market_ColData''_value(s: $2_vec_map_Entry'address_$0_market_ColData', x: $0_market_ColData): $2_vec_map_Entry'address_$0_market_ColData' {
    $2_vec_map_Entry'address_$0_market_ColData'($key#$2_vec_map_Entry'address_$0_market_ColData'(s), x)
}
function $IsValid'$2_vec_map_Entry'address_$0_market_ColData''(s: $2_vec_map_Entry'address_$0_market_ColData'): bool {
    $IsValid'address'($key#$2_vec_map_Entry'address_$0_market_ColData'(s))
      && $IsValid'$0_market_ColData'($value#$2_vec_map_Entry'address_$0_market_ColData'(s))
}
function {:inline} $IsEqual'$2_vec_map_Entry'address_$0_market_ColData''(s1: $2_vec_map_Entry'address_$0_market_ColData', s2: $2_vec_map_Entry'address_$0_market_ColData'): bool {
    s1 == s2
}

// struct vec_map::VecMap<address, market::ColData> at ./../sui/crates/sui-framework/sources/vec_map.move:26:5+94
type {:datatype} $2_vec_map_VecMap'address_$0_market_ColData';
function {:constructor} $2_vec_map_VecMap'address_$0_market_ColData'($contents: Vec ($2_vec_map_Entry'address_$0_market_ColData')): $2_vec_map_VecMap'address_$0_market_ColData';
function {:inline} $Update'$2_vec_map_VecMap'address_$0_market_ColData''_contents(s: $2_vec_map_VecMap'address_$0_market_ColData', x: Vec ($2_vec_map_Entry'address_$0_market_ColData')): $2_vec_map_VecMap'address_$0_market_ColData' {
    $2_vec_map_VecMap'address_$0_market_ColData'(x)
}
function $IsValid'$2_vec_map_VecMap'address_$0_market_ColData''(s: $2_vec_map_VecMap'address_$0_market_ColData'): bool {
    $IsValid'vec'$2_vec_map_Entry'address_$0_market_ColData'''($contents#$2_vec_map_VecMap'address_$0_market_ColData'(s))
}
function {:inline} $IsEqual'$2_vec_map_VecMap'address_$0_market_ColData''(s1: $2_vec_map_VecMap'address_$0_market_ColData', s2: $2_vec_map_VecMap'address_$0_market_ColData'): bool {
    $IsEqual'vec'$2_vec_map_Entry'address_$0_market_ColData'''($contents#$2_vec_map_VecMap'address_$0_market_ColData'(s1), $contents#$2_vec_map_VecMap'address_$0_market_ColData'(s2))}

// fun vec_map::contains<address, market::ColData> [baseline] at ./../sui/crates/sui-framework/sources/vec_map.move:72:5+124
procedure {:inline 1} $2_vec_map_contains'address_$0_market_ColData'(_$t0: $2_vec_map_VecMap'address_$0_market_ColData', _$t1: int) returns ($ret0: bool)
{
    // declare local variables
    var $t2: $1_option_Option'u64';
    var $t3: $1_option_Option'u64';
    var $t4: int;
    var $t5: bool;
    var $t0: $2_vec_map_VecMap'address_$0_market_ColData';
    var $t1: int;
    var $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'': $2_vec_map_VecMap'address_$0_market_ColData';
    var $temp_0'address': int;
    var $temp_0'bool': bool;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../sui/crates/sui-framework/sources/vec_map.move:72:5+1
    assume {:print "$at(6,2760,2761)"} true;
    assume {:print "$track_local(6,0,0):", $t0} $t0 == $t0;

    // trace_local[key]($t1) at ./../sui/crates/sui-framework/sources/vec_map.move:72:5+1
    assume {:print "$track_local(6,0,1):", $t1} $t1 == $t1;

    // $t3 := vec_map::get_idx_opt<#0, #1>($t0, $t1) on_abort goto L2 with $t4 at ./../sui/crates/sui-framework/sources/vec_map.move:73:26+22
    assume {:print "$at(6,2855,2877)"} true;
    call $t3 := $2_vec_map_get_idx_opt'address_$0_market_ColData'($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(6,2855,2877)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(6,0):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t5 := opaque begin: option::is_some<u64>($t3) at ./../sui/crates/sui-framework/sources/vec_map.move:73:9+40

    // assume WellFormed($t5) at ./../sui/crates/sui-framework/sources/vec_map.move:73:9+40
    assume $IsValid'bool'($t5);

    // assume Eq<bool>($t5, option::$is_some<u64>($t3)) at ./../sui/crates/sui-framework/sources/vec_map.move:73:9+40
    assume $IsEqual'bool'($t5, $1_option_$is_some'u64'($t3));

    // $t5 := opaque end: option::is_some<u64>($t3) at ./../sui/crates/sui-framework/sources/vec_map.move:73:9+40

    // trace_return[0]($t5) at ./../sui/crates/sui-framework/sources/vec_map.move:73:9+40
    assume {:print "$track_return(6,0,0):", $t5} $t5 == $t5;

    // label L1 at ./../sui/crates/sui-framework/sources/vec_map.move:74:5+1
    assume {:print "$at(6,2883,2884)"} true;
L1:

    // return $t5 at ./../sui/crates/sui-framework/sources/vec_map.move:74:5+1
    $ret0 := $t5;
    return;

    // label L2 at ./../sui/crates/sui-framework/sources/vec_map.move:74:5+1
L2:

    // abort($t4) at ./../sui/crates/sui-framework/sources/vec_map.move:74:5+1
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun vec_map::empty<address, market::ColData> [baseline] at ./../sui/crates/sui-framework/sources/vec_map.move:37:5+96
procedure {:inline 1} $2_vec_map_empty'address_$0_market_ColData'() returns ($ret0: $2_vec_map_VecMap'address_$0_market_ColData')
{
    // declare local variables
    var $t0: Vec ($2_vec_map_Entry'address_$0_market_ColData');
    var $t1: int;
    var $t2: $2_vec_map_VecMap'address_$0_market_ColData';
    var $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'': $2_vec_map_VecMap'address_$0_market_ColData';

    // bytecode translation starts here
    // $t0 := vector::empty<vec_map::Entry<#0, #1>>() on_abort goto L2 with $t1 at ./../sui/crates/sui-framework/sources/vec_map.move:38:28+15
    assume {:print "$at(6,1393,1408)"} true;
    call $t0 := $1_vector_empty'$2_vec_map_Entry'address_$0_market_ColData''();
    if ($abort_flag) {
        assume {:print "$at(6,1393,1408)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(6,2):", $t1} $t1 == $t1;
        goto L2;
    }

    // $t2 := pack vec_map::VecMap<#0, #1>($t0) at ./../sui/crates/sui-framework/sources/vec_map.move:38:9+36
    $t2 := $2_vec_map_VecMap'address_$0_market_ColData'($t0);

    // trace_return[0]($t2) at ./../sui/crates/sui-framework/sources/vec_map.move:38:9+36
    assume {:print "$track_return(6,2,0):", $t2} $t2 == $t2;

    // label L1 at ./../sui/crates/sui-framework/sources/vec_map.move:39:5+1
    assume {:print "$at(6,1415,1416)"} true;
L1:

    // return $t2 at ./../sui/crates/sui-framework/sources/vec_map.move:39:5+1
    $ret0 := $t2;
    return;

    // label L2 at ./../sui/crates/sui-framework/sources/vec_map.move:39:5+1
L2:

    // abort($t1) at ./../sui/crates/sui-framework/sources/vec_map.move:39:5+1
    $abort_code := $t1;
    $abort_flag := true;
    return;

}

// fun vec_map::get_idx<address, market::ColData> [baseline] at ./../sui/crates/sui-framework/sources/vec_map.move:129:5+218
procedure {:inline 1} $2_vec_map_get_idx'address_$0_market_ColData'(_$t0: $2_vec_map_VecMap'address_$0_market_ColData', _$t1: int) returns ($ret0: int)
{
    // declare local variables
    var $t2: $1_option_Option'u64';
    var $t3: $1_option_Option'u64';
    var $t4: int;
    var $t5: bool;
    var $t6: int;
    var $t7: int;
    var $t8: bool;
    var $t0: $2_vec_map_VecMap'address_$0_market_ColData';
    var $t1: int;
    var $temp_0'$1_option_Option'u64'': $1_option_Option'u64';
    var $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'': $2_vec_map_VecMap'address_$0_market_ColData';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../sui/crates/sui-framework/sources/vec_map.move:129:5+1
    assume {:print "$at(6,4974,4975)"} true;
    assume {:print "$track_local(6,6,0):", $t0} $t0 == $t0;

    // trace_local[key]($t1) at ./../sui/crates/sui-framework/sources/vec_map.move:129:5+1
    assume {:print "$track_local(6,6,1):", $t1} $t1 == $t1;

    // $t3 := vec_map::get_idx_opt<#0, #1>($t0, $t1) on_abort goto L3 with $t4 at ./../sui/crates/sui-framework/sources/vec_map.move:130:23+22
    assume {:print "$at(6,5063,5085)"} true;
    call $t3 := $2_vec_map_get_idx_opt'address_$0_market_ColData'($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(6,5063,5085)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(6,6):", $t4} $t4 == $t4;
        goto L3;
    }

    // trace_local[idx_opt]($t3) at ./../sui/crates/sui-framework/sources/vec_map.move:130:13+7
    assume {:print "$track_local(6,6,2):", $t3} $t3 == $t3;

    // $t5 := opaque begin: option::is_some<u64>($t3) at ./../sui/crates/sui-framework/sources/vec_map.move:131:17+25
    assume {:print "$at(6,5103,5128)"} true;

    // assume WellFormed($t5) at ./../sui/crates/sui-framework/sources/vec_map.move:131:17+25
    assume $IsValid'bool'($t5);

    // assume Eq<bool>($t5, option::$is_some<u64>($t3)) at ./../sui/crates/sui-framework/sources/vec_map.move:131:17+25
    assume $IsEqual'bool'($t5, $1_option_$is_some'u64'($t3));

    // $t5 := opaque end: option::is_some<u64>($t3) at ./../sui/crates/sui-framework/sources/vec_map.move:131:17+25

    // if ($t5) goto L0 else goto L1 at ./../sui/crates/sui-framework/sources/vec_map.move:131:9+52
    if ($t5) { goto L0; } else { goto L1; }

    // label L1 at ./../sui/crates/sui-framework/sources/vec_map.move:131:44+16
L1:

    // $t6 := 1 at ./../sui/crates/sui-framework/sources/vec_map.move:131:44+16
    $t6 := 1;
    assume $IsValid'u64'($t6);

    // trace_abort($t6) at ./../sui/crates/sui-framework/sources/vec_map.move:131:9+52
    assume {:print "$at(6,5095,5147)"} true;
    assume {:print "$track_abort(6,6):", $t6} $t6 == $t6;

    // $t4 := move($t6) at ./../sui/crates/sui-framework/sources/vec_map.move:131:9+52
    $t4 := $t6;

    // goto L3 at ./../sui/crates/sui-framework/sources/vec_map.move:131:9+52
    goto L3;

    // label L0 at ./../sui/crates/sui-framework/sources/vec_map.move:132:30+7
    assume {:print "$at(6,5178,5185)"} true;
L0:

    // $t7 := opaque begin: option::destroy_some<u64>($t3) at ./../sui/crates/sui-framework/sources/vec_map.move:132:9+29

    // assume Identical($t8, option::$is_none<u64>($t3)) at ./../sui/crates/sui-framework/sources/vec_map.move:132:9+29
    assume ($t8 == $1_option_$is_none'u64'($t3));

    // if ($t8) goto L5 else goto L4 at ./../sui/crates/sui-framework/sources/vec_map.move:132:9+29
    if ($t8) { goto L5; } else { goto L4; }

    // label L5 at ./../sui/crates/sui-framework/sources/vec_map.move:132:9+29
L5:

    // assume And(option::$is_none<u64>($t3), Eq(7, $t4)) at ./../sui/crates/sui-framework/sources/vec_map.move:132:9+29
    assume ($1_option_$is_none'u64'($t3) && $IsEqual'num'(7, $t4));

    // trace_abort($t4) at ./../sui/crates/sui-framework/sources/vec_map.move:132:9+29
    assume {:print "$at(6,5157,5186)"} true;
    assume {:print "$track_abort(6,6):", $t4} $t4 == $t4;

    // goto L3 at ./../sui/crates/sui-framework/sources/vec_map.move:132:9+29
    goto L3;

    // label L4 at ./../sui/crates/sui-framework/sources/vec_map.move:132:9+29
L4:

    // assume WellFormed($t7) at ./../sui/crates/sui-framework/sources/vec_map.move:132:9+29
    assume $IsValid'u64'($t7);

    // assume Eq<u64>($t7, option::$borrow<u64>($t3)) at ./../sui/crates/sui-framework/sources/vec_map.move:132:9+29
    assume $IsEqual'u64'($t7, $1_option_$borrow'u64'($t3));

    // $t7 := opaque end: option::destroy_some<u64>($t3) at ./../sui/crates/sui-framework/sources/vec_map.move:132:9+29

    // trace_return[0]($t7) at ./../sui/crates/sui-framework/sources/vec_map.move:132:9+29
    assume {:print "$track_return(6,6,0):", $t7} $t7 == $t7;

    // label L2 at ./../sui/crates/sui-framework/sources/vec_map.move:133:5+1
    assume {:print "$at(6,5191,5192)"} true;
L2:

    // return $t7 at ./../sui/crates/sui-framework/sources/vec_map.move:133:5+1
    $ret0 := $t7;
    return;

    // label L3 at ./../sui/crates/sui-framework/sources/vec_map.move:133:5+1
L3:

    // abort($t4) at ./../sui/crates/sui-framework/sources/vec_map.move:133:5+1
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun vec_map::get_idx_opt<address, market::ColData> [baseline] at ./../sui/crates/sui-framework/sources/vec_map.move:115:5+331
procedure {:inline 1} $2_vec_map_get_idx_opt'address_$0_market_ColData'(_$t0: $2_vec_map_VecMap'address_$0_market_ColData', _$t1: int) returns ($ret0: $1_option_Option'u64')
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: bool;
    var $t8: Vec ($2_vec_map_Entry'address_$0_market_ColData');
    var $t9: $2_vec_map_Entry'address_$0_market_ColData';
    var $t10: int;
    var $t11: bool;
    var $t12: int;
    var $t13: int;
    var $t14: $1_option_Option'u64';
    var $t15: $1_option_Option'u64';
    var $t16: $1_option_Option'u64';
    var $t0: $2_vec_map_VecMap'address_$0_market_ColData';
    var $t1: int;
    var $temp_0'$1_option_Option'u64'': $1_option_Option'u64';
    var $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'': $2_vec_map_VecMap'address_$0_market_ColData';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../sui/crates/sui-framework/sources/vec_map.move:115:5+1
    assume {:print "$at(6,4479,4480)"} true;
    assume {:print "$track_local(6,7,0):", $t0} $t0 == $t0;

    // trace_local[key]($t1) at ./../sui/crates/sui-framework/sources/vec_map.move:115:5+1
    assume {:print "$track_local(6,7,1):", $t1} $t1 == $t1;

    // $t4 := 0 at ./../sui/crates/sui-framework/sources/vec_map.move:116:17+1
    assume {:print "$at(6,4574,4575)"} true;
    $t4 := 0;
    assume $IsValid'u64'($t4);

    // trace_local[i]($t4) at ./../sui/crates/sui-framework/sources/vec_map.move:116:13+1
    assume {:print "$track_local(6,7,2):", $t4} $t4 == $t4;

    // $t5 := vec_map::size<#0, #1>($t0) on_abort goto L9 with $t6 at ./../sui/crates/sui-framework/sources/vec_map.move:117:17+10
    assume {:print "$at(6,4593,4603)"} true;
    call $t5 := $2_vec_map_size'address_$0_market_ColData'($t0);
    if ($abort_flag) {
        assume {:print "$at(6,4593,4603)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(6,7):", $t6} $t6 == $t6;
        goto L9;
    }

    // trace_local[n]($t5) at ./../sui/crates/sui-framework/sources/vec_map.move:117:13+1
    assume {:print "$track_local(6,7,3):", $t5} $t5 == $t5;

    // label L6 at ./../sui/crates/sui-framework/sources/vec_map.move:118:16+1
    assume {:print "$at(6,4620,4621)"} true;
L6:

    // havoc[val]($t4) at ./../sui/crates/sui-framework/sources/vec_map.move:118:16+1
    havoc $t4;
    assume $IsValid'u64'($t4);

    // havoc[val]($t7) at ./../sui/crates/sui-framework/sources/vec_map.move:118:16+1
    havoc $t7;
    assume $IsValid'bool'($t7);

    // havoc[val]($t8) at ./../sui/crates/sui-framework/sources/vec_map.move:118:16+1
    havoc $t8;
    assume $IsValid'vec'$2_vec_map_Entry'address_$0_market_ColData'''($t8);

    // havoc[val]($t9) at ./../sui/crates/sui-framework/sources/vec_map.move:118:16+1
    havoc $t9;
    assume $IsValid'$2_vec_map_Entry'address_$0_market_ColData''($t9);

    // havoc[val]($t10) at ./../sui/crates/sui-framework/sources/vec_map.move:118:16+1
    havoc $t10;
    assume $IsValid'address'($t10);

    // havoc[val]($t11) at ./../sui/crates/sui-framework/sources/vec_map.move:118:16+1
    havoc $t11;
    assume $IsValid'bool'($t11);

    // havoc[val]($t12) at ./../sui/crates/sui-framework/sources/vec_map.move:118:16+1
    havoc $t12;
    assume $IsValid'u64'($t12);

    // havoc[val]($t13) at ./../sui/crates/sui-framework/sources/vec_map.move:118:16+1
    havoc $t13;
    assume $IsValid'u64'($t13);

    // trace_local[i]($t4) at ./../sui/crates/sui-framework/sources/vec_map.move:118:16+1
    assume {:print "$info(): enter loop, variable(s) i havocked and reassigned"} true;
    assume {:print "$track_local(6,7,2):", $t4} $t4 == $t4;

    // assume Not(AbortFlag()) at ./../sui/crates/sui-framework/sources/vec_map.move:118:16+1
    assume !$abort_flag;

    // $t7 := <($t4, $t5) at ./../sui/crates/sui-framework/sources/vec_map.move:118:18+1
    call $t7 := $Lt($t4, $t5);

    // if ($t7) goto L0 else goto L2 at ./../sui/crates/sui-framework/sources/vec_map.move:118:9+167
    if ($t7) { goto L0; } else { goto L2; }

    // label L0 at ./../sui/crates/sui-framework/sources/vec_map.move:119:34+4
    assume {:print "$at(6,4662,4666)"} true;
L0:

    // $t8 := get_field<vec_map::VecMap<#0, #1>>.contents($t0) at ./../sui/crates/sui-framework/sources/vec_map.move:119:33+14
    $t8 := $contents#$2_vec_map_VecMap'address_$0_market_ColData'($t0);

    // $t9 := vector::borrow<vec_map::Entry<#0, #1>>($t8, $t4) on_abort goto L9 with $t6 at ./../sui/crates/sui-framework/sources/vec_map.move:119:18+33
    call $t9 := $1_vector_borrow'$2_vec_map_Entry'address_$0_market_ColData''($t8, $t4);
    if ($abort_flag) {
        assume {:print "$at(6,4646,4679)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(6,7):", $t6} $t6 == $t6;
        goto L9;
    }

    // $t10 := get_field<vec_map::Entry<#0, #1>>.key($t9) at ./../sui/crates/sui-framework/sources/vec_map.move:119:17+38
    $t10 := $key#$2_vec_map_Entry'address_$0_market_ColData'($t9);

    // $t11 := ==($t10, $t1) at ./../sui/crates/sui-framework/sources/vec_map.move:119:56+2
    $t11 := $IsEqual'address'($t10, $t1);

    // if ($t11) goto L3 else goto L5 at ./../sui/crates/sui-framework/sources/vec_map.move:119:13+105
    if ($t11) { goto L3; } else { goto L5; }

    // label L3 at ./../sui/crates/sui-framework/sources/vec_map.move:120:17+22
    assume {:print "$at(6,4710,4732)"} true;
L3:

    // destroy($t0) at ./../sui/crates/sui-framework/sources/vec_map.move:120:17+22

    // destroy($t1) at ./../sui/crates/sui-framework/sources/vec_map.move:120:17+22

    // $t14 := opaque begin: option::some<u64>($t4) at ./../sui/crates/sui-framework/sources/vec_map.move:120:24+15

    // assume And(WellFormed($t14), Le(Len<u64>(select option::Option.vec($t14)), 1)) at ./../sui/crates/sui-framework/sources/vec_map.move:120:24+15
    assume ($IsValid'$1_option_Option'u64''($t14) && (LenVec($vec#$1_option_Option'u64'($t14)) <= 1));

    // assume Eq<option::Option<u64>>($t14, option::spec_some<u64>($t4)) at ./../sui/crates/sui-framework/sources/vec_map.move:120:24+15
    assume $IsEqual'$1_option_Option'u64''($t14, $1_option_spec_some'u64'($t4));

    // $t14 := opaque end: option::some<u64>($t4) at ./../sui/crates/sui-framework/sources/vec_map.move:120:24+15

    // trace_return[0]($t14) at ./../sui/crates/sui-framework/sources/vec_map.move:120:17+22
    assume {:print "$track_return(6,7,0):", $t14} $t14 == $t14;

    // $t15 := move($t14) at ./../sui/crates/sui-framework/sources/vec_map.move:120:17+22
    $t15 := $t14;

    // goto L8 at ./../sui/crates/sui-framework/sources/vec_map.move:120:17+22
    goto L8;

    // label L5 at ./../sui/crates/sui-framework/sources/vec_map.move:122:17+1
    assume {:print "$at(6,4764,4765)"} true;
L5:

    // $t12 := 1 at ./../sui/crates/sui-framework/sources/vec_map.move:122:21+1
    $t12 := 1;
    assume $IsValid'u64'($t12);

    // $t13 := +($t4, $t12) on_abort goto L9 with $t6 at ./../sui/crates/sui-framework/sources/vec_map.move:122:19+1
    call $t13 := $AddU64($t4, $t12);
    if ($abort_flag) {
        assume {:print "$at(6,4766,4767)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(6,7):", $t6} $t6 == $t6;
        goto L9;
    }

    // trace_local[i]($t13) at ./../sui/crates/sui-framework/sources/vec_map.move:122:13+1
    assume {:print "$track_local(6,7,2):", $t13} $t13 == $t13;

    // goto L7 at ./../sui/crates/sui-framework/sources/vec_map.move:122:22+1
    goto L7;

    // label L2 at ./../sui/crates/sui-framework/sources/vec_map.move:124:9+14
    assume {:print "$at(6,4790,4804)"} true;
L2:

    // destroy($t0) at ./../sui/crates/sui-framework/sources/vec_map.move:124:9+14

    // destroy($t1) at ./../sui/crates/sui-framework/sources/vec_map.move:124:9+14

    // $t16 := opaque begin: option::none<u64>() at ./../sui/crates/sui-framework/sources/vec_map.move:124:9+14

    // assume And(WellFormed($t16), Le(Len<u64>(select option::Option.vec($t16)), 1)) at ./../sui/crates/sui-framework/sources/vec_map.move:124:9+14
    assume ($IsValid'$1_option_Option'u64''($t16) && (LenVec($vec#$1_option_Option'u64'($t16)) <= 1));

    // assume Eq<option::Option<u64>>($t16, option::spec_none<u64>()) at ./../sui/crates/sui-framework/sources/vec_map.move:124:9+14
    assume $IsEqual'$1_option_Option'u64''($t16, $1_option_spec_none'u64'());

    // $t16 := opaque end: option::none<u64>() at ./../sui/crates/sui-framework/sources/vec_map.move:124:9+14

    // trace_return[0]($t16) at ./../sui/crates/sui-framework/sources/vec_map.move:124:9+14
    assume {:print "$track_return(6,7,0):", $t16} $t16 == $t16;

    // $t15 := move($t16) at ./../sui/crates/sui-framework/sources/vec_map.move:124:9+14
    $t15 := $t16;

    // goto L8 at ./../sui/crates/sui-framework/sources/vec_map.move:124:9+14
    goto L8;

    // label L7 at ./../sui/crates/sui-framework/sources/vec_map.move:124:9+14
    // Loop invariant checking block for the loop started with header: L6
L7:

    // stop() at ./../sui/crates/sui-framework/sources/vec_map.move:124:9+14
    assume false;
    return;

    // label L8 at ./../sui/crates/sui-framework/sources/vec_map.move:125:5+1
    assume {:print "$at(6,4809,4810)"} true;
L8:

    // return $t15 at ./../sui/crates/sui-framework/sources/vec_map.move:125:5+1
    $ret0 := $t15;
    return;

    // label L9 at ./../sui/crates/sui-framework/sources/vec_map.move:125:5+1
L9:

    // abort($t6) at ./../sui/crates/sui-framework/sources/vec_map.move:125:5+1
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun vec_map::insert<address, market::ColData> [baseline] at ./../sui/crates/sui-framework/sources/vec_map.move:43:5+206
procedure {:inline 1} $2_vec_map_insert'address_$0_market_ColData'(_$t0: $Mutation ($2_vec_map_VecMap'address_$0_market_ColData'), _$t1: int, _$t2: $0_market_ColData) returns ($ret0: $Mutation ($2_vec_map_VecMap'address_$0_market_ColData'))
{
    // declare local variables
    var $t3: $Mutation ($2_vec_map_VecMap'address_$0_market_ColData');
    var $t4: int;
    var $t5: $2_vec_map_VecMap'address_$0_market_ColData';
    var $t6: bool;
    var $t7: int;
    var $t8: bool;
    var $t9: int;
    var $t10: $Mutation (Vec ($2_vec_map_Entry'address_$0_market_ColData'));
    var $t11: $2_vec_map_Entry'address_$0_market_ColData';
    var $t0: $Mutation ($2_vec_map_VecMap'address_$0_market_ColData');
    var $t1: int;
    var $t2: $0_market_ColData;
    var $temp_0'$0_market_ColData': $0_market_ColData;
    var $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'': $2_vec_map_VecMap'address_$0_market_ColData';
    var $temp_0'address': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;
    assume IsEmptyVec(p#$Mutation($t3));
    assume IsEmptyVec(p#$Mutation($t10));

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../sui/crates/sui-framework/sources/vec_map.move:43:5+1
    assume {:print "$at(6,1528,1529)"} true;
    $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' := $Dereference($t0);
    assume {:print "$track_local(6,9,0):", $temp_0'$2_vec_map_VecMap'address_$0_market_ColData''} $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' == $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'';

    // trace_local[key]($t1) at ./../sui/crates/sui-framework/sources/vec_map.move:43:5+1
    assume {:print "$track_local(6,9,1):", $t1} $t1 == $t1;

    // trace_local[value]($t2) at ./../sui/crates/sui-framework/sources/vec_map.move:43:5+1
    assume {:print "$track_local(6,9,2):", $t2} $t2 == $t2;

    // $t5 := read_ref($t0) at ./../sui/crates/sui-framework/sources/vec_map.move:44:26+12
    assume {:print "$at(6,1627,1639)"} true;
    $t5 := $Dereference($t0);

    // $t6 := vec_map::contains<#0, #1>($t5, $t1) on_abort goto L3 with $t7 at ./../sui/crates/sui-framework/sources/vec_map.move:44:18+20
    call $t6 := $2_vec_map_contains'address_$0_market_ColData'($t5, $t1);
    if ($abort_flag) {
        assume {:print "$at(6,1619,1639)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(6,9):", $t7} $t7 == $t7;
        goto L3;
    }

    // $t8 := !($t6) at ./../sui/crates/sui-framework/sources/vec_map.move:44:17+1
    call $t8 := $Not($t6);

    // if ($t8) goto L0 else goto L1 at ./../sui/crates/sui-framework/sources/vec_map.move:44:9+49
    if ($t8) { goto L0; } else { goto L1; }

    // label L1 at ./../sui/crates/sui-framework/sources/vec_map.move:44:9+49
L1:

    // destroy($t0) at ./../sui/crates/sui-framework/sources/vec_map.move:44:9+49

    // $t9 := 0 at ./../sui/crates/sui-framework/sources/vec_map.move:44:40+17
    $t9 := 0;
    assume $IsValid'u64'($t9);

    // trace_abort($t9) at ./../sui/crates/sui-framework/sources/vec_map.move:44:9+49
    assume {:print "$at(6,1610,1659)"} true;
    assume {:print "$track_abort(6,9):", $t9} $t9 == $t9;

    // $t7 := move($t9) at ./../sui/crates/sui-framework/sources/vec_map.move:44:9+49
    $t7 := $t9;

    // goto L3 at ./../sui/crates/sui-framework/sources/vec_map.move:44:9+49
    goto L3;

    // label L0 at ./../sui/crates/sui-framework/sources/vec_map.move:45:32+4
    assume {:print "$at(6,1692,1696)"} true;
L0:

    // $t10 := borrow_field<vec_map::VecMap<#0, #1>>.contents($t0) at ./../sui/crates/sui-framework/sources/vec_map.move:45:27+18
    $t10 := $ChildMutation($t0, 0, $contents#$2_vec_map_VecMap'address_$0_market_ColData'($Dereference($t0)));

    // $t11 := pack vec_map::Entry<#0, #1>($t1, $t2) at ./../sui/crates/sui-framework/sources/vec_map.move:45:47+20
    $t11 := $2_vec_map_Entry'address_$0_market_ColData'($t1, $t2);

    // vector::push_back<vec_map::Entry<#0, #1>>($t10, $t11) on_abort goto L3 with $t7 at ./../sui/crates/sui-framework/sources/vec_map.move:45:9+59
    call $t10 := $1_vector_push_back'$2_vec_map_Entry'address_$0_market_ColData''($t10, $t11);
    if ($abort_flag) {
        assume {:print "$at(6,1669,1728)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(6,9):", $t7} $t7 == $t7;
        goto L3;
    }

    // write_back[Reference($t0).contents (vector<vec_map::Entry<#0, #1>>)]($t10) at ./../sui/crates/sui-framework/sources/vec_map.move:45:9+59
    $t0 := $UpdateMutation($t0, $Update'$2_vec_map_VecMap'address_$0_market_ColData''_contents($Dereference($t0), $Dereference($t10)));

    // trace_local[self]($t0) at ./../sui/crates/sui-framework/sources/vec_map.move:45:9+59
    $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' := $Dereference($t0);
    assume {:print "$track_local(6,9,0):", $temp_0'$2_vec_map_VecMap'address_$0_market_ColData''} $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' == $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'';

    // trace_local[self]($t0) at ./../sui/crates/sui-framework/sources/vec_map.move:45:9+59
    $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' := $Dereference($t0);
    assume {:print "$track_local(6,9,0):", $temp_0'$2_vec_map_VecMap'address_$0_market_ColData''} $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' == $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'';

    // label L2 at ./../sui/crates/sui-framework/sources/vec_map.move:46:5+1
    assume {:print "$at(6,1733,1734)"} true;
L2:

    // return () at ./../sui/crates/sui-framework/sources/vec_map.move:46:5+1
    $ret0 := $t0;
    return;

    // label L3 at ./../sui/crates/sui-framework/sources/vec_map.move:46:5+1
L3:

    // abort($t7) at ./../sui/crates/sui-framework/sources/vec_map.move:46:5+1
    $abort_code := $t7;
    $abort_flag := true;
    return;

}

// fun vec_map::size<address, market::ColData> [baseline] at ./../sui/crates/sui-framework/sources/vec_map.move:77:5+99
procedure {:inline 1} $2_vec_map_size'address_$0_market_ColData'(_$t0: $2_vec_map_VecMap'address_$0_market_ColData') returns ($ret0: int)
{
    // declare local variables
    var $t1: Vec ($2_vec_map_Entry'address_$0_market_ColData');
    var $t2: int;
    var $t3: int;
    var $t0: $2_vec_map_VecMap'address_$0_market_ColData';
    var $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'': $2_vec_map_VecMap'address_$0_market_ColData';
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../sui/crates/sui-framework/sources/vec_map.move:77:5+1
    assume {:print "$at(6,2937,2938)"} true;
    assume {:print "$track_local(6,13,0):", $t0} $t0 == $t0;

    // $t1 := get_field<vec_map::VecMap<#0, #1>>.contents($t0) at ./../sui/crates/sui-framework/sources/vec_map.move:78:24+14
    assume {:print "$at(6,3015,3029)"} true;
    $t1 := $contents#$2_vec_map_VecMap'address_$0_market_ColData'($t0);

    // $t2 := vector::length<vec_map::Entry<#0, #1>>($t1) on_abort goto L2 with $t3 at ./../sui/crates/sui-framework/sources/vec_map.move:78:9+30
    call $t2 := $1_vector_length'$2_vec_map_Entry'address_$0_market_ColData''($t1);
    if ($abort_flag) {
        assume {:print "$at(6,3000,3030)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(6,13):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_return[0]($t2) at ./../sui/crates/sui-framework/sources/vec_map.move:78:9+30
    assume {:print "$track_return(6,13,0):", $t2} $t2 == $t2;

    // label L1 at ./../sui/crates/sui-framework/sources/vec_map.move:79:5+1
    assume {:print "$at(6,3035,3036)"} true;
L1:

    // return $t2 at ./../sui/crates/sui-framework/sources/vec_map.move:79:5+1
    $ret0 := $t2;
    return;

    // label L2 at ./../sui/crates/sui-framework/sources/vec_map.move:79:5+1
L2:

    // abort($t3) at ./../sui/crates/sui-framework/sources/vec_map.move:79:5+1
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun vec_map::get<address, market::ColData> [baseline] at ./../sui/crates/sui-framework/sources/vec_map.move:65:5+183
procedure {:inline 1} $2_vec_map_get'address_$0_market_ColData'(_$t0: $2_vec_map_VecMap'address_$0_market_ColData', _$t1: int) returns ($ret0: $0_market_ColData)
{
    // declare local variables
    var $t2: $2_vec_map_Entry'address_$0_market_ColData';
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: Vec ($2_vec_map_Entry'address_$0_market_ColData');
    var $t7: $2_vec_map_Entry'address_$0_market_ColData';
    var $t8: $0_market_ColData;
    var $t0: $2_vec_map_VecMap'address_$0_market_ColData';
    var $t1: int;
    var $temp_0'$0_market_ColData': $0_market_ColData;
    var $temp_0'$2_vec_map_Entry'address_$0_market_ColData'': $2_vec_map_Entry'address_$0_market_ColData';
    var $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'': $2_vec_map_VecMap'address_$0_market_ColData';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../sui/crates/sui-framework/sources/vec_map.move:65:5+1
    assume {:print "$at(6,2496,2497)"} true;
    assume {:print "$track_local(6,3,0):", $t0} $t0 == $t0;

    // trace_local[key]($t1) at ./../sui/crates/sui-framework/sources/vec_map.move:65:5+1
    assume {:print "$track_local(6,3,1):", $t1} $t1 == $t1;

    // $t4 := vec_map::get_idx<#0, #1>($t0, $t1) on_abort goto L2 with $t5 at ./../sui/crates/sui-framework/sources/vec_map.move:66:19+18
    assume {:print "$at(6,2576,2594)"} true;
    call $t4 := $2_vec_map_get_idx'address_$0_market_ColData'($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(6,2576,2594)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(6,3):", $t5} $t5 == $t5;
        goto L2;
    }

    // trace_local[idx]($t4) at ./../sui/crates/sui-framework/sources/vec_map.move:66:13+3
    assume {:print "$track_local(6,3,3):", $t4} $t4 == $t4;

    // $t6 := get_field<vec_map::VecMap<#0, #1>>.contents($t0) at ./../sui/crates/sui-framework/sources/vec_map.move:67:36+14
    assume {:print "$at(6,2631,2645)"} true;
    $t6 := $contents#$2_vec_map_VecMap'address_$0_market_ColData'($t0);

    // $t7 := vector::borrow<vec_map::Entry<#0, #1>>($t6, $t4) on_abort goto L2 with $t5 at ./../sui/crates/sui-framework/sources/vec_map.move:67:21+35
    call $t7 := $1_vector_borrow'$2_vec_map_Entry'address_$0_market_ColData''($t6, $t4);
    if ($abort_flag) {
        assume {:print "$at(6,2616,2651)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(6,3):", $t5} $t5 == $t5;
        goto L2;
    }

    // trace_local[entry]($t7) at ./../sui/crates/sui-framework/sources/vec_map.move:67:13+5
    assume {:print "$track_local(6,3,2):", $t7} $t7 == $t7;

    // $t8 := get_field<vec_map::Entry<#0, #1>>.value($t7) at ./../sui/crates/sui-framework/sources/vec_map.move:68:9+12
    assume {:print "$at(6,2661,2673)"} true;
    $t8 := $value#$2_vec_map_Entry'address_$0_market_ColData'($t7);

    // trace_return[0]($t8) at ./../sui/crates/sui-framework/sources/vec_map.move:68:9+12
    assume {:print "$track_return(6,3,0):", $t8} $t8 == $t8;

    // label L1 at ./../sui/crates/sui-framework/sources/vec_map.move:69:5+1
    assume {:print "$at(6,2678,2679)"} true;
L1:

    // return $t8 at ./../sui/crates/sui-framework/sources/vec_map.move:69:5+1
    $ret0 := $t8;
    return;

    // label L2 at ./../sui/crates/sui-framework/sources/vec_map.move:69:5+1
L2:

    // abort($t5) at ./../sui/crates/sui-framework/sources/vec_map.move:69:5+1
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun vec_map::get_mut<address, market::ColData> [baseline] at ./../sui/crates/sui-framework/sources/vec_map.move:57:5+207
procedure {:inline 1} $2_vec_map_get_mut'address_$0_market_ColData'(_$t0: $Mutation ($2_vec_map_VecMap'address_$0_market_ColData'), _$t1: int) returns ($ret0: $Mutation ($0_market_ColData), $ret1: $Mutation ($2_vec_map_VecMap'address_$0_market_ColData'))
{
    // declare local variables
    var $t2: $Mutation ($2_vec_map_VecMap'address_$0_market_ColData');
    var $t3: int;
    var $t4: $Mutation ($2_vec_map_Entry'address_$0_market_ColData');
    var $t5: int;
    var $t6: $2_vec_map_VecMap'address_$0_market_ColData';
    var $t7: int;
    var $t8: int;
    var $t9: $Mutation (Vec ($2_vec_map_Entry'address_$0_market_ColData'));
    var $t10: $Mutation ($2_vec_map_Entry'address_$0_market_ColData');
    var $t11: $Mutation ($0_market_ColData);
    var $t0: $Mutation ($2_vec_map_VecMap'address_$0_market_ColData');
    var $t1: int;
    var $temp_0'$0_market_ColData': $0_market_ColData;
    var $temp_0'$2_vec_map_Entry'address_$0_market_ColData'': $2_vec_map_Entry'address_$0_market_ColData';
    var $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'': $2_vec_map_VecMap'address_$0_market_ColData';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    assume IsEmptyVec(p#$Mutation($t2));
    assume IsEmptyVec(p#$Mutation($t4));
    assume IsEmptyVec(p#$Mutation($t9));
    assume IsEmptyVec(p#$Mutation($t10));
    assume IsEmptyVec(p#$Mutation($t11));

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../sui/crates/sui-framework/sources/vec_map.move:57:5+1
    assume {:print "$at(6,2172,2173)"} true;
    $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' := $Dereference($t0);
    assume {:print "$track_local(6,8,0):", $temp_0'$2_vec_map_VecMap'address_$0_market_ColData''} $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' == $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'';

    // trace_local[key]($t1) at ./../sui/crates/sui-framework/sources/vec_map.move:57:5+1
    assume {:print "$track_local(6,8,1):", $t1} $t1 == $t1;

    // $t6 := read_ref($t0) at ./../sui/crates/sui-framework/sources/vec_map.move:58:26+11
    assume {:print "$at(6,2271,2282)"} true;
    $t6 := $Dereference($t0);

    // $t7 := vec_map::get_idx<#0, #1>($t6, $t1) on_abort goto L2 with $t8 at ./../sui/crates/sui-framework/sources/vec_map.move:58:19+18
    call $t7 := $2_vec_map_get_idx'address_$0_market_ColData'($t6, $t1);
    if ($abort_flag) {
        assume {:print "$at(6,2264,2282)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(6,8):", $t8} $t8 == $t8;
        goto L2;
    }

    // trace_local[idx]($t7) at ./../sui/crates/sui-framework/sources/vec_map.move:58:13+3
    assume {:print "$track_local(6,8,5):", $t7} $t7 == $t7;

    // $t9 := borrow_field<vec_map::VecMap<#0, #1>>.contents($t0) at ./../sui/crates/sui-framework/sources/vec_map.move:59:40+18
    assume {:print "$at(6,2323,2341)"} true;
    $t9 := $ChildMutation($t0, 0, $contents#$2_vec_map_VecMap'address_$0_market_ColData'($Dereference($t0)));

    // $t10 := vector::borrow_mut<vec_map::Entry<#0, #1>>($t9, $t7) on_abort goto L2 with $t8 at ./../sui/crates/sui-framework/sources/vec_map.move:59:21+43
    call $t10,$t9 := $1_vector_borrow_mut'$2_vec_map_Entry'address_$0_market_ColData''($t9, $t7);
    if ($abort_flag) {
        assume {:print "$at(6,2304,2347)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(6,8):", $t8} $t8 == $t8;
        goto L2;
    }

    // trace_local[entry]($t10) at ./../sui/crates/sui-framework/sources/vec_map.move:59:13+5
    $temp_0'$2_vec_map_Entry'address_$0_market_ColData'' := $Dereference($t10);
    assume {:print "$track_local(6,8,4):", $temp_0'$2_vec_map_Entry'address_$0_market_ColData''} $temp_0'$2_vec_map_Entry'address_$0_market_ColData'' == $temp_0'$2_vec_map_Entry'address_$0_market_ColData'';

    // $t11 := borrow_field<vec_map::Entry<#0, #1>>.value($t10) at ./../sui/crates/sui-framework/sources/vec_map.move:60:9+16
    assume {:print "$at(6,2357,2373)"} true;
    $t11 := $ChildMutation($t10, 1, $value#$2_vec_map_Entry'address_$0_market_ColData'($Dereference($t10)));

    // trace_return[0]($t11) at ./../sui/crates/sui-framework/sources/vec_map.move:60:9+16
    $temp_0'$0_market_ColData' := $Dereference($t11);
    assume {:print "$track_return(6,8,0):", $temp_0'$0_market_ColData'} $temp_0'$0_market_ColData' == $temp_0'$0_market_ColData';

    // trace_local[self]($t0) at ./../sui/crates/sui-framework/sources/vec_map.move:60:9+16
    $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' := $Dereference($t0);
    assume {:print "$track_local(6,8,0):", $temp_0'$2_vec_map_VecMap'address_$0_market_ColData''} $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' == $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'';

    // trace_local[self]($t0) at ./../sui/crates/sui-framework/sources/vec_map.move:60:9+16
    $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' := $Dereference($t0);
    assume {:print "$track_local(6,8,0):", $temp_0'$2_vec_map_VecMap'address_$0_market_ColData''} $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' == $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'';

    // label L1 at ./../sui/crates/sui-framework/sources/vec_map.move:61:5+1
    assume {:print "$at(6,2378,2379)"} true;
L1:

    // return $t11 at ./../sui/crates/sui-framework/sources/vec_map.move:61:5+1
    $ret0 := $t11;
    $ret1 := $t0;
    return;

    // label L2 at ./../sui/crates/sui-framework/sources/vec_map.move:61:5+1
L2:

    // abort($t8) at ./../sui/crates/sui-framework/sources/vec_map.move:61:5+1
    $abort_code := $t8;
    $abort_flag := true;
    return;

}

// fun signer::address_of [baseline] at ./../sui/crates/sui-framework/deps/move-stdlib/sources/signer.move:15:5+77
procedure {:inline 1} $1_signer_address_of(_$t0: $signer) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t0: $signer;
    var $temp_0'address': int;
    var $temp_0'signer': $signer;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[s]($t0) at ./../sui/crates/sui-framework/deps/move-stdlib/sources/signer.move:15:5+1
    assume {:print "$at(28,470,471)"} true;
    assume {:print "$track_local(7,0,0):", $t0} $t0 == $t0;

    // $t1 := signer::borrow_address($t0) on_abort goto L2 with $t2 at ./../sui/crates/sui-framework/deps/move-stdlib/sources/signer.move:16:10+17
    assume {:print "$at(28,524,541)"} true;
    call $t1 := $1_signer_borrow_address($t0);
    if ($abort_flag) {
        assume {:print "$at(28,524,541)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(7,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_return[0]($t1) at ./../sui/crates/sui-framework/deps/move-stdlib/sources/signer.move:16:9+18
    assume {:print "$track_return(7,0,0):", $t1} $t1 == $t1;

    // label L1 at ./../sui/crates/sui-framework/deps/move-stdlib/sources/signer.move:17:5+1
    assume {:print "$at(28,546,547)"} true;
L1:

    // return $t1 at ./../sui/crates/sui-framework/deps/move-stdlib/sources/signer.move:17:5+1
    $ret0 := $t1;
    return;

    // label L2 at ./../sui/crates/sui-framework/deps/move-stdlib/sources/signer.move:17:5+1
L2:

    // abort($t2) at ./../sui/crates/sui-framework/deps/move-stdlib/sources/signer.move:17:5+1
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// struct tx_context::TxContext at ./../sui/crates/sui-framework/sources/tx_context.move:25:5+453
type {:datatype} $2_tx_context_TxContext;
function {:constructor} $2_tx_context_TxContext($signer: $signer, $tx_hash: Vec (int), $epoch: int, $ids_created: int): $2_tx_context_TxContext;
function {:inline} $Update'$2_tx_context_TxContext'_signer(s: $2_tx_context_TxContext, x: $signer): $2_tx_context_TxContext {
    $2_tx_context_TxContext(x, $tx_hash#$2_tx_context_TxContext(s), $epoch#$2_tx_context_TxContext(s), $ids_created#$2_tx_context_TxContext(s))
}
function {:inline} $Update'$2_tx_context_TxContext'_tx_hash(s: $2_tx_context_TxContext, x: Vec (int)): $2_tx_context_TxContext {
    $2_tx_context_TxContext($signer#$2_tx_context_TxContext(s), x, $epoch#$2_tx_context_TxContext(s), $ids_created#$2_tx_context_TxContext(s))
}
function {:inline} $Update'$2_tx_context_TxContext'_epoch(s: $2_tx_context_TxContext, x: int): $2_tx_context_TxContext {
    $2_tx_context_TxContext($signer#$2_tx_context_TxContext(s), $tx_hash#$2_tx_context_TxContext(s), x, $ids_created#$2_tx_context_TxContext(s))
}
function {:inline} $Update'$2_tx_context_TxContext'_ids_created(s: $2_tx_context_TxContext, x: int): $2_tx_context_TxContext {
    $2_tx_context_TxContext($signer#$2_tx_context_TxContext(s), $tx_hash#$2_tx_context_TxContext(s), $epoch#$2_tx_context_TxContext(s), x)
}
function $IsValid'$2_tx_context_TxContext'(s: $2_tx_context_TxContext): bool {
    $IsValid'signer'($signer#$2_tx_context_TxContext(s))
      && $IsValid'vec'u8''($tx_hash#$2_tx_context_TxContext(s))
      && $IsValid'u64'($epoch#$2_tx_context_TxContext(s))
      && $IsValid'u64'($ids_created#$2_tx_context_TxContext(s))
}
function {:inline} $IsEqual'$2_tx_context_TxContext'(s1: $2_tx_context_TxContext, s2: $2_tx_context_TxContext): bool {
    $IsEqual'signer'($signer#$2_tx_context_TxContext(s1), $signer#$2_tx_context_TxContext(s2))
    && $IsEqual'vec'u8''($tx_hash#$2_tx_context_TxContext(s1), $tx_hash#$2_tx_context_TxContext(s2))
    && $IsEqual'u64'($epoch#$2_tx_context_TxContext(s1), $epoch#$2_tx_context_TxContext(s2))
    && $IsEqual'u64'($ids_created#$2_tx_context_TxContext(s1), $ids_created#$2_tx_context_TxContext(s2))}

// fun tx_context::new_object [baseline] at ./../sui/crates/sui-framework/sources/tx_context.move:53:5+220
procedure {:inline 1} $2_tx_context_new_object(_$t0: $Mutation ($2_tx_context_TxContext)) returns ($ret0: int, $ret1: $Mutation ($2_tx_context_TxContext))
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: int;
    var $t4: Vec (int);
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: int;
    var $t9: $Mutation (int);
    var $t0: $Mutation ($2_tx_context_TxContext);
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    assume IsEmptyVec(p#$Mutation($t9));

    // bytecode translation starts here
    // trace_local[ctx]($t0) at ./../sui/crates/sui-framework/sources/tx_context.move:53:5+1
    assume {:print "$at(45,1734,1735)"} true;
    $temp_0'$2_tx_context_TxContext' := $Dereference($t0);
    assume {:print "$track_local(8,3,0):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // $t3 := get_field<tx_context::TxContext>.ids_created($t0) at ./../sui/crates/sui-framework/sources/tx_context.move:54:27+15
    assume {:print "$at(45,1822,1837)"} true;
    $t3 := $ids_created#$2_tx_context_TxContext($Dereference($t0));

    // trace_local[ids_created]($t3) at ./../sui/crates/sui-framework/sources/tx_context.move:54:13+11
    assume {:print "$track_local(8,3,2):", $t3} $t3 == $t3;

    // $t4 := get_field<tx_context::TxContext>.tx_hash($t0) at ./../sui/crates/sui-framework/sources/tx_context.move:55:29+12
    assume {:print "$at(45,1867,1879)"} true;
    $t4 := $tx_hash#$2_tx_context_TxContext($Dereference($t0));

    // $t5 := tx_context::derive_id($t4, $t3) on_abort goto L2 with $t6 at ./../sui/crates/sui-framework/sources/tx_context.move:55:18+37
    call $t5 := $2_tx_context_derive_id($t4, $t3);
    if ($abort_flag) {
        assume {:print "$at(45,1856,1893)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(8,3):", $t6} $t6 == $t6;
        goto L2;
    }

    // trace_local[id]($t5) at ./../sui/crates/sui-framework/sources/tx_context.move:55:13+2
    assume {:print "$track_local(8,3,1):", $t5} $t5 == $t5;

    // $t7 := 1 at ./../sui/crates/sui-framework/sources/tx_context.move:56:41+1
    assume {:print "$at(45,1935,1936)"} true;
    $t7 := 1;
    assume $IsValid'u64'($t7);

    // $t8 := +($t3, $t7) on_abort goto L2 with $t6 at ./../sui/crates/sui-framework/sources/tx_context.move:56:39+1
    call $t8 := $AddU64($t3, $t7);
    if ($abort_flag) {
        assume {:print "$at(45,1933,1934)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(8,3):", $t6} $t6 == $t6;
        goto L2;
    }

    // $t9 := borrow_field<tx_context::TxContext>.ids_created($t0) at ./../sui/crates/sui-framework/sources/tx_context.move:56:9+15
    $t9 := $ChildMutation($t0, 3, $ids_created#$2_tx_context_TxContext($Dereference($t0)));

    // write_ref($t9, $t8) at ./../sui/crates/sui-framework/sources/tx_context.move:56:9+33
    $t9 := $UpdateMutation($t9, $t8);

    // write_back[Reference($t0).ids_created (u64)]($t9) at ./../sui/crates/sui-framework/sources/tx_context.move:56:9+33
    $t0 := $UpdateMutation($t0, $Update'$2_tx_context_TxContext'_ids_created($Dereference($t0), $Dereference($t9)));

    // trace_local[ctx]($t0) at ./../sui/crates/sui-framework/sources/tx_context.move:56:9+33
    $temp_0'$2_tx_context_TxContext' := $Dereference($t0);
    assume {:print "$track_local(8,3,0):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // trace_return[0]($t5) at ./../sui/crates/sui-framework/sources/tx_context.move:57:9+2
    assume {:print "$at(45,1946,1948)"} true;
    assume {:print "$track_return(8,3,0):", $t5} $t5 == $t5;

    // trace_local[ctx]($t0) at ./../sui/crates/sui-framework/sources/tx_context.move:57:9+2
    $temp_0'$2_tx_context_TxContext' := $Dereference($t0);
    assume {:print "$track_local(8,3,0):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // label L1 at ./../sui/crates/sui-framework/sources/tx_context.move:58:5+1
    assume {:print "$at(45,1953,1954)"} true;
L1:

    // return $t5 at ./../sui/crates/sui-framework/sources/tx_context.move:58:5+1
    $ret0 := $t5;
    $ret1 := $t0;
    return;

    // label L2 at ./../sui/crates/sui-framework/sources/tx_context.move:58:5+1
L2:

    // abort($t6) at ./../sui/crates/sui-framework/sources/tx_context.move:58:5+1
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun tx_context::sender [baseline] at ./../sui/crates/sui-framework/sources/tx_context.move:39:5+93
procedure {:inline 1} $2_tx_context_sender(_$t0: $2_tx_context_TxContext) returns ($ret0: int)
{
    // declare local variables
    var $t1: $signer;
    var $t2: int;
    var $t3: int;
    var $t0: $2_tx_context_TxContext;
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $temp_0'address': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../sui/crates/sui-framework/sources/tx_context.move:39:5+1
    assume {:print "$at(45,1343,1344)"} true;
    assume {:print "$track_local(8,4,0):", $t0} $t0 == $t0;

    // $t1 := get_field<tx_context::TxContext>.signer($t0) at ./../sui/crates/sui-framework/sources/tx_context.move:40:28+12
    assume {:print "$at(45,1417,1429)"} true;
    $t1 := $signer#$2_tx_context_TxContext($t0);

    // $t2 := signer::address_of($t1) on_abort goto L2 with $t3 at ./../sui/crates/sui-framework/sources/tx_context.move:40:9+32
    call $t2 := $1_signer_address_of($t1);
    if ($abort_flag) {
        assume {:print "$at(45,1398,1430)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(8,4):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_return[0]($t2) at ./../sui/crates/sui-framework/sources/tx_context.move:40:9+32
    assume {:print "$track_return(8,4,0):", $t2} $t2 == $t2;

    // label L1 at ./../sui/crates/sui-framework/sources/tx_context.move:41:5+1
    assume {:print "$at(45,1435,1436)"} true;
L1:

    // return $t2 at ./../sui/crates/sui-framework/sources/tx_context.move:41:5+1
    $ret0 := $t2;
    return;

    // label L2 at ./../sui/crates/sui-framework/sources/tx_context.move:41:5+1
L2:

    // abort($t3) at ./../sui/crates/sui-framework/sources/tx_context.move:41:5+1
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// struct object::ID at ./../sui/crates/sui-framework/sources/object.move:24:5+406
type {:datatype} $2_object_ID;
function {:constructor} $2_object_ID($bytes: int): $2_object_ID;
function {:inline} $Update'$2_object_ID'_bytes(s: $2_object_ID, x: int): $2_object_ID {
    $2_object_ID(x)
}
function $IsValid'$2_object_ID'(s: $2_object_ID): bool {
    $IsValid'address'($bytes#$2_object_ID(s))
}
function {:inline} $IsEqual'$2_object_ID'(s1: $2_object_ID, s2: $2_object_ID): bool {
    s1 == s2
}

// struct object::UID at ./../sui/crates/sui-framework/sources/object.move:38:5+44
type {:datatype} $2_object_UID;
function {:constructor} $2_object_UID($id: $2_object_ID): $2_object_UID;
function {:inline} $Update'$2_object_UID'_id(s: $2_object_UID, x: $2_object_ID): $2_object_UID {
    $2_object_UID(x)
}
function $IsValid'$2_object_UID'(s: $2_object_UID): bool {
    $IsValid'$2_object_ID'($id#$2_object_UID(s))
}
function {:inline} $IsEqual'$2_object_UID'(s1: $2_object_UID, s2: $2_object_UID): bool {
    s1 == s2
}

// fun object::borrow_id<market::Market> [baseline] at ./../sui/crates/sui-framework/sources/object.move:109:5+78
procedure {:inline 1} $2_object_borrow_id'$0_market_Market'(_$t0: $0_market_Market) returns ($ret0: $2_object_ID)
{
    // declare local variables
    var $t1: $2_object_UID;
    var $t2: int;
    var $t3: $2_object_ID;
    var $t0: $0_market_Market;
    var $temp_0'$0_market_Market': $0_market_Market;
    var $temp_0'$2_object_ID': $2_object_ID;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[obj]($t0) at ./../sui/crates/sui-framework/sources/object.move:109:5+1
    assume {:print "$at(4,3831,3832)"} true;
    assume {:print "$track_local(10,0,0):", $t0} $t0 == $t0;

    // $t1 := object::borrow_uid<#0>($t0) on_abort goto L2 with $t2 at ./../sui/crates/sui-framework/sources/object.move:110:10+15
    assume {:print "$at(4,3885,3900)"} true;
    call $t1 := $2_object_borrow_uid'$0_market_Market'($t0);
    if ($abort_flag) {
        assume {:print "$at(4,3885,3900)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(10,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := get_field<object::UID>.id($t1) at ./../sui/crates/sui-framework/sources/object.move:110:9+19
    $t3 := $id#$2_object_UID($t1);

    // trace_return[0]($t3) at ./../sui/crates/sui-framework/sources/object.move:110:9+19
    assume {:print "$track_return(10,0,0):", $t3} $t3 == $t3;

    // label L1 at ./../sui/crates/sui-framework/sources/object.move:111:5+1
    assume {:print "$at(4,3908,3909)"} true;
L1:

    // return $t3 at ./../sui/crates/sui-framework/sources/object.move:111:5+1
    $ret0 := $t3;
    return;

    // label L2 at ./../sui/crates/sui-framework/sources/object.move:111:5+1
L2:

    // abort($t2) at ./../sui/crates/sui-framework/sources/object.move:111:5+1
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun object::delete [baseline] at ./../sui/crates/sui-framework/sources/object.move:99:5+58
procedure {:inline 1} $2_object_delete(_$t0: $2_object_UID) returns ()
{
    // declare local variables
    var $t1: int;
    var $t0: $2_object_UID;
    var $temp_0'$2_object_UID': $2_object_UID;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[id]($t0) at ./../sui/crates/sui-framework/sources/object.move:99:5+1
    assume {:print "$at(4,3607,3608)"} true;
    assume {:print "$track_local(10,3,0):", $t0} $t0 == $t0;

    // object::delete_impl<object::UID>($t0) on_abort goto L2 with $t1 at ./../sui/crates/sui-framework/sources/object.move:100:9+15
    assume {:print "$at(4,3644,3659)"} true;
    call $2_object_delete_impl'$2_object_UID'($t0);
    if ($abort_flag) {
        assume {:print "$at(4,3644,3659)"} true;
        $t1 := $abort_code;
        assume {:print "$track_abort(10,3):", $t1} $t1 == $t1;
        goto L2;
    }

    // label L1 at ./../sui/crates/sui-framework/sources/object.move:101:5+1
    assume {:print "$at(4,3664,3665)"} true;
L1:

    // return () at ./../sui/crates/sui-framework/sources/object.move:101:5+1
    return;

    // label L2 at ./../sui/crates/sui-framework/sources/object.move:101:5+1
L2:

    // abort($t1) at ./../sui/crates/sui-framework/sources/object.move:101:5+1
    $abort_code := $t1;
    $abort_flag := true;
    return;

}

// fun object::id_address<market::Market> [baseline] at ./../sui/crates/sui-framework/sources/object.move:119:5+88
procedure {:inline 1} $2_object_id_address'$0_market_Market'(_$t0: $0_market_Market) returns ($ret0: int)
{
    // declare local variables
    var $t1: $2_object_UID;
    var $t2: int;
    var $t3: $2_object_ID;
    var $t4: int;
    var $t0: $0_market_Market;
    var $temp_0'$0_market_Market': $0_market_Market;
    var $temp_0'address': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[obj]($t0) at ./../sui/crates/sui-framework/sources/object.move:119:5+1
    assume {:print "$at(4,4140,4141)"} true;
    assume {:print "$track_local(10,6,0):", $t0} $t0 == $t0;

    // $t1 := object::borrow_uid<#0>($t0) on_abort goto L2 with $t2 at ./../sui/crates/sui-framework/sources/object.move:120:9+15
    assume {:print "$at(4,4198,4213)"} true;
    call $t1 := $2_object_borrow_uid'$0_market_Market'($t0);
    if ($abort_flag) {
        assume {:print "$at(4,4198,4213)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(10,6):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := get_field<object::UID>.id($t1) at ./../sui/crates/sui-framework/sources/object.move:120:9+18
    $t3 := $id#$2_object_UID($t1);

    // $t4 := get_field<object::ID>.bytes($t3) at ./../sui/crates/sui-framework/sources/object.move:120:9+24
    $t4 := $bytes#$2_object_ID($t3);

    // trace_return[0]($t4) at ./../sui/crates/sui-framework/sources/object.move:120:9+24
    assume {:print "$track_return(10,6,0):", $t4} $t4 == $t4;

    // label L1 at ./../sui/crates/sui-framework/sources/object.move:121:5+1
    assume {:print "$at(4,4227,4228)"} true;
L1:

    // return $t4 at ./../sui/crates/sui-framework/sources/object.move:121:5+1
    $ret0 := $t4;
    return;

    // label L2 at ./../sui/crates/sui-framework/sources/object.move:121:5+1
L2:

    // abort($t2) at ./../sui/crates/sui-framework/sources/object.move:121:5+1
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun object::new [baseline] at ./../sui/crates/sui-framework/sources/object.move:88:5+131
procedure {:inline 1} $2_object_new(_$t0: $Mutation ($2_tx_context_TxContext)) returns ($ret0: $2_object_UID, $ret1: $Mutation ($2_tx_context_TxContext))
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: $2_object_ID;
    var $t4: $2_object_UID;
    var $t0: $Mutation ($2_tx_context_TxContext);
    var $temp_0'$2_object_UID': $2_object_UID;
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[ctx]($t0) at ./../sui/crates/sui-framework/sources/object.move:88:5+1
    assume {:print "$at(4,3114,3115)"} true;
    $temp_0'$2_tx_context_TxContext' := $Dereference($t0);
    assume {:print "$track_local(10,10,0):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // $t1 := tx_context::new_object($t0) on_abort goto L2 with $t2 at ./../sui/crates/sui-framework/sources/object.move:90:29+27
    assume {:print "$at(4,3199,3226)"} true;
    call $t1,$t0 := $2_tx_context_new_object($t0);
    if ($abort_flag) {
        assume {:print "$at(4,3199,3226)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(10,10):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := pack object::ID($t1) at ./../sui/crates/sui-framework/sources/object.move:90:17+41
    $t3 := $2_object_ID($t1);

    // $t4 := pack object::UID($t3) at ./../sui/crates/sui-framework/sources/object.move:89:9+74
    assume {:print "$at(4,3165,3239)"} true;
    $t4 := $2_object_UID($t3);

    // trace_return[0]($t4) at ./../sui/crates/sui-framework/sources/object.move:89:9+74
    assume {:print "$track_return(10,10,0):", $t4} $t4 == $t4;

    // trace_local[ctx]($t0) at ./../sui/crates/sui-framework/sources/object.move:89:9+74
    $temp_0'$2_tx_context_TxContext' := $Dereference($t0);
    assume {:print "$track_local(10,10,0):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // label L1 at ./../sui/crates/sui-framework/sources/object.move:92:5+1
    assume {:print "$at(4,3244,3245)"} true;
L1:

    // return $t4 at ./../sui/crates/sui-framework/sources/object.move:92:5+1
    $ret0 := $t4;
    $ret1 := $t0;
    return;

    // label L2 at ./../sui/crates/sui-framework/sources/object.move:92:5+1
L2:

    // abort($t2) at ./../sui/crates/sui-framework/sources/object.move:92:5+1
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun object::uid_to_inner [baseline] at ./../sui/crates/sui-framework/sources/object.move:70:5+61
procedure {:inline 1} $2_object_uid_to_inner(_$t0: $2_object_UID) returns ($ret0: $2_object_ID)
{
    // declare local variables
    var $t1: $2_object_ID;
    var $t0: $2_object_UID;
    var $temp_0'$2_object_ID': $2_object_ID;
    var $temp_0'$2_object_UID': $2_object_UID;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[uid]($t0) at ./../sui/crates/sui-framework/sources/object.move:70:5+1
    assume {:print "$at(4,2624,2625)"} true;
    assume {:print "$track_local(10,15,0):", $t0} $t0 == $t0;

    // $t1 := get_field<object::UID>.id($t0) at ./../sui/crates/sui-framework/sources/object.move:71:9+6
    assume {:print "$at(4,2673,2679)"} true;
    $t1 := $id#$2_object_UID($t0);

    // trace_return[0]($t1) at ./../sui/crates/sui-framework/sources/object.move:71:9+6
    assume {:print "$track_return(10,15,0):", $t1} $t1 == $t1;

    // label L1 at ./../sui/crates/sui-framework/sources/object.move:72:5+1
    assume {:print "$at(4,2684,2685)"} true;
L1:

    // return $t1 at ./../sui/crates/sui-framework/sources/object.move:72:5+1
    $ret0 := $t1;
    return;

}

// fun transfer::transfer<market::AdminCap> [baseline] at ./../sui/crates/sui-framework/sources/transfer.move:10:5+140
procedure {:inline 1} $2_transfer_transfer'$0_market_AdminCap'(_$t0: $0_market_AdminCap, _$t1: int) returns ()
{
    // declare local variables
    var $t2: bool;
    var $t3: int;
    var $t0: $0_market_AdminCap;
    var $t1: int;
    var $temp_0'$0_market_AdminCap': $0_market_AdminCap;
    var $temp_0'address': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[obj]($t0) at ./../sui/crates/sui-framework/sources/transfer.move:10:5+1
    assume {:print "$at(61,309,310)"} true;
    assume {:print "$track_local(11,2,0):", $t0} $t0 == $t0;

    // trace_local[recipient]($t1) at ./../sui/crates/sui-framework/sources/transfer.move:10:5+1
    assume {:print "$track_local(11,2,1):", $t1} $t1 == $t1;

    // $t2 := false at ./../sui/crates/sui-framework/sources/transfer.move:12:43+5
    assume {:print "$at(61,437,442)"} true;
    $t2 := false;
    assume $IsValid'bool'($t2);

    // transfer::transfer_internal<#0>($t0, $t1, $t2) on_abort goto L2 with $t3 at ./../sui/crates/sui-framework/sources/transfer.move:12:9+40
    call $2_transfer_transfer_internal'$0_market_AdminCap'($t0, $t1, $t2);
    if ($abort_flag) {
        assume {:print "$at(61,403,443)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(11,2):", $t3} $t3 == $t3;
        goto L2;
    }

    // label L1 at ./../sui/crates/sui-framework/sources/transfer.move:13:5+1
    assume {:print "$at(61,448,449)"} true;
L1:

    // return () at ./../sui/crates/sui-framework/sources/transfer.move:13:5+1
    return;

    // label L2 at ./../sui/crates/sui-framework/sources/transfer.move:13:5+1
L2:

    // abort($t3) at ./../sui/crates/sui-framework/sources/transfer.move:13:5+1
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun transfer::transfer_to_object<market::BorrowRecord<#0, #1>, market::Market> [baseline] at ./../sui/crates/sui-framework/sources/transfer.move:16:5+174
procedure {:inline 1} $2_transfer_transfer_to_object'$0_market_BorrowRecord'#0_#1'_$0_market_Market'(_$t0: $0_market_BorrowRecord'#0_#1', _$t1: $Mutation ($0_market_Market)) returns ($ret0: $Mutation ($0_market_Market))
{
    // declare local variables
    var $t2: int;
    var $t3: $0_market_Market;
    var $t4: int;
    var $t5: int;
    var $t6: bool;
    var $t0: $0_market_BorrowRecord'#0_#1';
    var $t1: $Mutation ($0_market_Market);
    var $temp_0'$0_market_BorrowRecord'#0_#1'': $0_market_BorrowRecord'#0_#1';
    var $temp_0'$0_market_Market': $0_market_Market;
    var $temp_0'address': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[obj]($t0) at ./../sui/crates/sui-framework/sources/transfer.move:16:5+1
    assume {:print "$at(61,518,519)"} true;
    assume {:print "$track_local(11,4,0):", $t0} $t0 == $t0;

    // trace_local[owner]($t1) at ./../sui/crates/sui-framework/sources/transfer.move:16:5+1
    $temp_0'$0_market_Market' := $Dereference($t1);
    assume {:print "$track_local(11,4,1):", $temp_0'$0_market_Market'} $temp_0'$0_market_Market' == $temp_0'$0_market_Market';

    // $t3 := read_ref($t1) at ./../sui/crates/sui-framework/sources/transfer.move:17:43+5
    assume {:print "$at(61,631,636)"} true;
    $t3 := $Dereference($t1);

    // $t4 := object::id_address<#1>($t3) on_abort goto L2 with $t5 at ./../sui/crates/sui-framework/sources/transfer.move:17:24+25
    call $t4 := $2_object_id_address'$0_market_Market'($t3);
    if ($abort_flag) {
        assume {:print "$at(61,612,637)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(11,4):", $t5} $t5 == $t5;
        goto L2;
    }

    // trace_local[owner_id]($t4) at ./../sui/crates/sui-framework/sources/transfer.move:17:13+8
    assume {:print "$track_local(11,4,2):", $t4} $t4 == $t4;

    // $t6 := true at ./../sui/crates/sui-framework/sources/transfer.move:18:42+4
    assume {:print "$at(61,680,684)"} true;
    $t6 := true;
    assume $IsValid'bool'($t6);

    // transfer::transfer_internal<#0>($t0, $t4, $t6) on_abort goto L2 with $t5 at ./../sui/crates/sui-framework/sources/transfer.move:18:9+38
    call $2_transfer_transfer_internal'$0_market_BorrowRecord'#0_#1''($t0, $t4, $t6);
    if ($abort_flag) {
        assume {:print "$at(61,647,685)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(11,4):", $t5} $t5 == $t5;
        goto L2;
    }

    // trace_local[owner]($t1) at ./../sui/crates/sui-framework/sources/transfer.move:18:47+1
    $temp_0'$0_market_Market' := $Dereference($t1);
    assume {:print "$track_local(11,4,1):", $temp_0'$0_market_Market'} $temp_0'$0_market_Market' == $temp_0'$0_market_Market';

    // label L1 at ./../sui/crates/sui-framework/sources/transfer.move:19:5+1
    assume {:print "$at(61,691,692)"} true;
L1:

    // return () at ./../sui/crates/sui-framework/sources/transfer.move:19:5+1
    $ret0 := $t1;
    return;

    // label L2 at ./../sui/crates/sui-framework/sources/transfer.move:19:5+1
L2:

    // abort($t5) at ./../sui/crates/sui-framework/sources/transfer.move:19:5+1
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun transfer::transfer_to_object<market::SubMarket<#0>, market::Market> [baseline] at ./../sui/crates/sui-framework/sources/transfer.move:16:5+174
procedure {:inline 1} $2_transfer_transfer_to_object'$0_market_SubMarket'#0'_$0_market_Market'(_$t0: $0_market_SubMarket'#0', _$t1: $Mutation ($0_market_Market)) returns ($ret0: $Mutation ($0_market_Market))
{
    // declare local variables
    var $t2: int;
    var $t3: $0_market_Market;
    var $t4: int;
    var $t5: int;
    var $t6: bool;
    var $t0: $0_market_SubMarket'#0';
    var $t1: $Mutation ($0_market_Market);
    var $temp_0'$0_market_Market': $0_market_Market;
    var $temp_0'$0_market_SubMarket'#0'': $0_market_SubMarket'#0';
    var $temp_0'address': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[obj]($t0) at ./../sui/crates/sui-framework/sources/transfer.move:16:5+1
    assume {:print "$at(61,518,519)"} true;
    assume {:print "$track_local(11,4,0):", $t0} $t0 == $t0;

    // trace_local[owner]($t1) at ./../sui/crates/sui-framework/sources/transfer.move:16:5+1
    $temp_0'$0_market_Market' := $Dereference($t1);
    assume {:print "$track_local(11,4,1):", $temp_0'$0_market_Market'} $temp_0'$0_market_Market' == $temp_0'$0_market_Market';

    // $t3 := read_ref($t1) at ./../sui/crates/sui-framework/sources/transfer.move:17:43+5
    assume {:print "$at(61,631,636)"} true;
    $t3 := $Dereference($t1);

    // $t4 := object::id_address<#1>($t3) on_abort goto L2 with $t5 at ./../sui/crates/sui-framework/sources/transfer.move:17:24+25
    call $t4 := $2_object_id_address'$0_market_Market'($t3);
    if ($abort_flag) {
        assume {:print "$at(61,612,637)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(11,4):", $t5} $t5 == $t5;
        goto L2;
    }

    // trace_local[owner_id]($t4) at ./../sui/crates/sui-framework/sources/transfer.move:17:13+8
    assume {:print "$track_local(11,4,2):", $t4} $t4 == $t4;

    // $t6 := true at ./../sui/crates/sui-framework/sources/transfer.move:18:42+4
    assume {:print "$at(61,680,684)"} true;
    $t6 := true;
    assume $IsValid'bool'($t6);

    // transfer::transfer_internal<#0>($t0, $t4, $t6) on_abort goto L2 with $t5 at ./../sui/crates/sui-framework/sources/transfer.move:18:9+38
    call $2_transfer_transfer_internal'$0_market_SubMarket'#0''($t0, $t4, $t6);
    if ($abort_flag) {
        assume {:print "$at(61,647,685)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(11,4):", $t5} $t5 == $t5;
        goto L2;
    }

    // trace_local[owner]($t1) at ./../sui/crates/sui-framework/sources/transfer.move:18:47+1
    $temp_0'$0_market_Market' := $Dereference($t1);
    assume {:print "$track_local(11,4,1):", $temp_0'$0_market_Market'} $temp_0'$0_market_Market' == $temp_0'$0_market_Market';

    // label L1 at ./../sui/crates/sui-framework/sources/transfer.move:19:5+1
    assume {:print "$at(61,691,692)"} true;
L1:

    // return () at ./../sui/crates/sui-framework/sources/transfer.move:19:5+1
    $ret0 := $t1;
    return;

    // label L2 at ./../sui/crates/sui-framework/sources/transfer.move:19:5+1
L2:

    // abort($t5) at ./../sui/crates/sui-framework/sources/transfer.move:19:5+1
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// struct balance::Balance<#0> at ./../sui/crates/sui-framework/sources/balance.move:27:5+62
type {:datatype} $2_balance_Balance'#0';
function {:constructor} $2_balance_Balance'#0'($value: int): $2_balance_Balance'#0';
function {:inline} $Update'$2_balance_Balance'#0''_value(s: $2_balance_Balance'#0', x: int): $2_balance_Balance'#0' {
    $2_balance_Balance'#0'(x)
}
function $IsValid'$2_balance_Balance'#0''(s: $2_balance_Balance'#0'): bool {
    $IsValid'u64'($value#$2_balance_Balance'#0'(s))
}
function {:inline} $IsEqual'$2_balance_Balance'#0''(s1: $2_balance_Balance'#0', s2: $2_balance_Balance'#0'): bool {
    s1 == s2
}

// struct balance::Balance<#1> at ./../sui/crates/sui-framework/sources/balance.move:27:5+62
type {:datatype} $2_balance_Balance'#1';
function {:constructor} $2_balance_Balance'#1'($value: int): $2_balance_Balance'#1';
function {:inline} $Update'$2_balance_Balance'#1''_value(s: $2_balance_Balance'#1', x: int): $2_balance_Balance'#1' {
    $2_balance_Balance'#1'(x)
}
function $IsValid'$2_balance_Balance'#1''(s: $2_balance_Balance'#1'): bool {
    $IsValid'u64'($value#$2_balance_Balance'#1'(s))
}
function {:inline} $IsEqual'$2_balance_Balance'#1''(s1: $2_balance_Balance'#1', s2: $2_balance_Balance'#1'): bool {
    s1 == s2
}

// fun balance::value<#0> [baseline] at ./../sui/crates/sui-framework/sources/balance.move:32:5+70
procedure {:inline 1} $2_balance_value'#0'(_$t0: $2_balance_Balance'#0') returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t0: $2_balance_Balance'#0';
    var $temp_0'$2_balance_Balance'#0'': $2_balance_Balance'#0';
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../sui/crates/sui-framework/sources/balance.move:32:5+1
    assume {:print "$at(8,1083,1084)"} true;
    assume {:print "$track_local(13,7,0):", $t0} $t0 == $t0;

    // $t1 := get_field<balance::Balance<#0>>.value($t0) at ./../sui/crates/sui-framework/sources/balance.move:33:9+10
    assume {:print "$at(8,1137,1147)"} true;
    $t1 := $value#$2_balance_Balance'#0'($t0);

    // trace_return[0]($t1) at ./../sui/crates/sui-framework/sources/balance.move:33:9+10
    assume {:print "$track_return(13,7,0):", $t1} $t1 == $t1;

    // label L1 at ./../sui/crates/sui-framework/sources/balance.move:34:5+1
    assume {:print "$at(8,1152,1153)"} true;
L1:

    // return $t1 at ./../sui/crates/sui-framework/sources/balance.move:34:5+1
    $ret0 := $t1;
    return;

}

// fun balance::join<#0> [baseline] at ./../sui/crates/sui-framework/sources/balance.move:72:5+176
procedure {:inline 1} $2_balance_join'#0'(_$t0: $Mutation ($2_balance_Balance'#0'), _$t1: $2_balance_Balance'#0') returns ($ret0: int, $ret1: $Mutation ($2_balance_Balance'#0'))
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: $Mutation (int);
    var $t8: int;
    var $t0: $Mutation ($2_balance_Balance'#0');
    var $t1: $2_balance_Balance'#0';
    var $temp_0'$2_balance_Balance'#0'': $2_balance_Balance'#0';
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    assume IsEmptyVec(p#$Mutation($t7));

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../sui/crates/sui-framework/sources/balance.move:72:5+1
    assume {:print "$at(8,2249,2250)"} true;
    $temp_0'$2_balance_Balance'#0'' := $Dereference($t0);
    assume {:print "$track_local(13,4,0):", $temp_0'$2_balance_Balance'#0''} $temp_0'$2_balance_Balance'#0'' == $temp_0'$2_balance_Balance'#0'';

    // trace_local[balance]($t1) at ./../sui/crates/sui-framework/sources/balance.move:72:5+1
    assume {:print "$track_local(13,4,1):", $t1} $t1 == $t1;

    // $t3 := unpack balance::Balance<#0>($t1) at ./../sui/crates/sui-framework/sources/balance.move:73:13+17
    assume {:print "$at(8,2331,2348)"} true;
    $t3 := $value#$2_balance_Balance'#0'($t1);

    // trace_local[value]($t3) at ./../sui/crates/sui-framework/sources/balance.move:73:23+5
    assume {:print "$track_local(13,4,2):", $t3} $t3 == $t3;

    // $t4 := get_field<balance::Balance<#0>>.value($t0) at ./../sui/crates/sui-framework/sources/balance.move:74:22+10
    assume {:print "$at(8,2381,2391)"} true;
    $t4 := $value#$2_balance_Balance'#0'($Dereference($t0));

    // $t5 := +($t4, $t3) on_abort goto L2 with $t6 at ./../sui/crates/sui-framework/sources/balance.move:74:33+1
    call $t5 := $AddU64($t4, $t3);
    if ($abort_flag) {
        assume {:print "$at(8,2392,2393)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(13,4):", $t6} $t6 == $t6;
        goto L2;
    }

    // $t7 := borrow_field<balance::Balance<#0>>.value($t0) at ./../sui/crates/sui-framework/sources/balance.move:74:9+10
    $t7 := $ChildMutation($t0, 0, $value#$2_balance_Balance'#0'($Dereference($t0)));

    // write_ref($t7, $t5) at ./../sui/crates/sui-framework/sources/balance.move:74:9+31
    $t7 := $UpdateMutation($t7, $t5);

    // write_back[Reference($t0).value (u64)]($t7) at ./../sui/crates/sui-framework/sources/balance.move:74:9+31
    $t0 := $UpdateMutation($t0, $Update'$2_balance_Balance'#0''_value($Dereference($t0), $Dereference($t7)));

    // trace_local[self]($t0) at ./../sui/crates/sui-framework/sources/balance.move:74:9+31
    $temp_0'$2_balance_Balance'#0'' := $Dereference($t0);
    assume {:print "$track_local(13,4,0):", $temp_0'$2_balance_Balance'#0''} $temp_0'$2_balance_Balance'#0'' == $temp_0'$2_balance_Balance'#0'';

    // $t8 := get_field<balance::Balance<#0>>.value($t0) at ./../sui/crates/sui-framework/sources/balance.move:75:9+10
    assume {:print "$at(8,2409,2419)"} true;
    $t8 := $value#$2_balance_Balance'#0'($Dereference($t0));

    // trace_return[0]($t8) at ./../sui/crates/sui-framework/sources/balance.move:75:9+10
    assume {:print "$track_return(13,4,0):", $t8} $t8 == $t8;

    // trace_local[self]($t0) at ./../sui/crates/sui-framework/sources/balance.move:75:9+10
    $temp_0'$2_balance_Balance'#0'' := $Dereference($t0);
    assume {:print "$track_local(13,4,0):", $temp_0'$2_balance_Balance'#0''} $temp_0'$2_balance_Balance'#0'' == $temp_0'$2_balance_Balance'#0'';

    // label L1 at ./../sui/crates/sui-framework/sources/balance.move:76:5+1
    assume {:print "$at(8,2424,2425)"} true;
L1:

    // return $t8 at ./../sui/crates/sui-framework/sources/balance.move:76:5+1
    $ret0 := $t8;
    $ret1 := $t0;
    return;

    // label L2 at ./../sui/crates/sui-framework/sources/balance.move:76:5+1
L2:

    // abort($t6) at ./../sui/crates/sui-framework/sources/balance.move:76:5+1
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun balance::split<#0> [baseline] at ./../sui/crates/sui-framework/sources/balance.move:84:5+191
procedure {:inline 1} $2_balance_split'#0'(_$t0: $Mutation ($2_balance_Balance'#0'), _$t1: int) returns ($ret0: $2_balance_Balance'#0', $ret1: $Mutation ($2_balance_Balance'#0'))
{
    // declare local variables
    var $t2: int;
    var $t3: bool;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: int;
    var $t8: $Mutation (int);
    var $t9: $2_balance_Balance'#0';
    var $t0: $Mutation ($2_balance_Balance'#0');
    var $t1: int;
    var $temp_0'$2_balance_Balance'#0'': $2_balance_Balance'#0';
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    assume IsEmptyVec(p#$Mutation($t8));

    // bytecode translation starts here
    // trace_local[self]($t0) at ./../sui/crates/sui-framework/sources/balance.move:84:5+1
    assume {:print "$at(8,2613,2614)"} true;
    $temp_0'$2_balance_Balance'#0'' := $Dereference($t0);
    assume {:print "$track_local(13,5,0):", $temp_0'$2_balance_Balance'#0''} $temp_0'$2_balance_Balance'#0'' == $temp_0'$2_balance_Balance'#0'';

    // trace_local[value]($t1) at ./../sui/crates/sui-framework/sources/balance.move:84:5+1
    assume {:print "$track_local(13,5,1):", $t1} $t1 == $t1;

    // $t2 := get_field<balance::Balance<#0>>.value($t0) at ./../sui/crates/sui-framework/sources/balance.move:85:17+10
    assume {:print "$at(8,2698,2708)"} true;
    $t2 := $value#$2_balance_Balance'#0'($Dereference($t0));

    // $t3 := >=($t2, $t1) at ./../sui/crates/sui-framework/sources/balance.move:85:28+2
    call $t3 := $Ge($t2, $t1);

    // if ($t3) goto L0 else goto L1 at ./../sui/crates/sui-framework/sources/balance.move:85:9+40
    if ($t3) { goto L0; } else { goto L1; }

    // label L1 at ./../sui/crates/sui-framework/sources/balance.move:85:9+40
L1:

    // destroy($t0) at ./../sui/crates/sui-framework/sources/balance.move:85:9+40

    // $t4 := 2 at ./../sui/crates/sui-framework/sources/balance.move:85:38+10
    $t4 := 2;
    assume $IsValid'u64'($t4);

    // trace_abort($t4) at ./../sui/crates/sui-framework/sources/balance.move:85:9+40
    assume {:print "$at(8,2690,2730)"} true;
    assume {:print "$track_abort(13,5):", $t4} $t4 == $t4;

    // $t5 := move($t4) at ./../sui/crates/sui-framework/sources/balance.move:85:9+40
    $t5 := $t4;

    // goto L3 at ./../sui/crates/sui-framework/sources/balance.move:85:9+40
    goto L3;

    // label L0 at ./../sui/crates/sui-framework/sources/balance.move:86:22+4
    assume {:print "$at(8,2753,2757)"} true;
L0:

    // $t6 := get_field<balance::Balance<#0>>.value($t0) at ./../sui/crates/sui-framework/sources/balance.move:86:22+10
    $t6 := $value#$2_balance_Balance'#0'($Dereference($t0));

    // $t7 := -($t6, $t1) on_abort goto L3 with $t5 at ./../sui/crates/sui-framework/sources/balance.move:86:33+1
    call $t7 := $Sub($t6, $t1);
    if ($abort_flag) {
        assume {:print "$at(8,2764,2765)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(13,5):", $t5} $t5 == $t5;
        goto L3;
    }

    // $t8 := borrow_field<balance::Balance<#0>>.value($t0) at ./../sui/crates/sui-framework/sources/balance.move:86:9+10
    $t8 := $ChildMutation($t0, 0, $value#$2_balance_Balance'#0'($Dereference($t0)));

    // write_ref($t8, $t7) at ./../sui/crates/sui-framework/sources/balance.move:86:9+31
    $t8 := $UpdateMutation($t8, $t7);

    // write_back[Reference($t0).value (u64)]($t8) at ./../sui/crates/sui-framework/sources/balance.move:86:9+31
    $t0 := $UpdateMutation($t0, $Update'$2_balance_Balance'#0''_value($Dereference($t0), $Dereference($t8)));

    // trace_local[self]($t0) at ./../sui/crates/sui-framework/sources/balance.move:86:9+31
    $temp_0'$2_balance_Balance'#0'' := $Dereference($t0);
    assume {:print "$track_local(13,5,0):", $temp_0'$2_balance_Balance'#0''} $temp_0'$2_balance_Balance'#0'' == $temp_0'$2_balance_Balance'#0'';

    // $t9 := pack balance::Balance<#0>($t1) at ./../sui/crates/sui-framework/sources/balance.move:87:9+17
    assume {:print "$at(8,2781,2798)"} true;
    $t9 := $2_balance_Balance'#0'($t1);

    // trace_return[0]($t9) at ./../sui/crates/sui-framework/sources/balance.move:87:9+17
    assume {:print "$track_return(13,5,0):", $t9} $t9 == $t9;

    // trace_local[self]($t0) at ./../sui/crates/sui-framework/sources/balance.move:87:9+17
    $temp_0'$2_balance_Balance'#0'' := $Dereference($t0);
    assume {:print "$track_local(13,5,0):", $temp_0'$2_balance_Balance'#0''} $temp_0'$2_balance_Balance'#0'' == $temp_0'$2_balance_Balance'#0'';

    // label L2 at ./../sui/crates/sui-framework/sources/balance.move:88:5+1
    assume {:print "$at(8,2803,2804)"} true;
L2:

    // return $t9 at ./../sui/crates/sui-framework/sources/balance.move:88:5+1
    $ret0 := $t9;
    $ret1 := $t0;
    return;

    // label L3 at ./../sui/crates/sui-framework/sources/balance.move:88:5+1
L3:

    // abort($t5) at ./../sui/crates/sui-framework/sources/balance.move:88:5+1
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun balance::zero<#0> [baseline] at ./../sui/crates/sui-framework/sources/balance.move:62:5+69
procedure {:inline 1} $2_balance_zero'#0'() returns ($ret0: $2_balance_Balance'#0')
{
    // declare local variables
    var $t0: int;
    var $t1: $2_balance_Balance'#0';
    var $temp_0'$2_balance_Balance'#0'': $2_balance_Balance'#0';

    // bytecode translation starts here
    // $t0 := 0 at ./../sui/crates/sui-framework/sources/balance.move:63:26+1
    assume {:print "$at(8,2115,2116)"} true;
    $t0 := 0;
    assume $IsValid'u64'($t0);

    // $t1 := pack balance::Balance<#0>($t0) at ./../sui/crates/sui-framework/sources/balance.move:63:9+20
    $t1 := $2_balance_Balance'#0'($t0);

    // trace_return[0]($t1) at ./../sui/crates/sui-framework/sources/balance.move:63:9+20
    assume {:print "$track_return(13,8,0):", $t1} $t1 == $t1;

    // label L1 at ./../sui/crates/sui-framework/sources/balance.move:64:5+1
    assume {:print "$at(8,2123,2124)"} true;
L1:

    // return $t1 at ./../sui/crates/sui-framework/sources/balance.move:64:5+1
    $ret0 := $t1;
    return;

}

// struct coin::Coin<#0> at ./../sui/crates/sui-framework/sources/coin.move:15:5+90
type {:datatype} $2_coin_Coin'#0';
function {:constructor} $2_coin_Coin'#0'($id: $2_object_UID, $balance: $2_balance_Balance'#0'): $2_coin_Coin'#0';
function {:inline} $Update'$2_coin_Coin'#0''_id(s: $2_coin_Coin'#0', x: $2_object_UID): $2_coin_Coin'#0' {
    $2_coin_Coin'#0'(x, $balance#$2_coin_Coin'#0'(s))
}
function {:inline} $Update'$2_coin_Coin'#0''_balance(s: $2_coin_Coin'#0', x: $2_balance_Balance'#0'): $2_coin_Coin'#0' {
    $2_coin_Coin'#0'($id#$2_coin_Coin'#0'(s), x)
}
function $IsValid'$2_coin_Coin'#0''(s: $2_coin_Coin'#0'): bool {
    $IsValid'$2_object_UID'($id#$2_coin_Coin'#0'(s))
      && $IsValid'$2_balance_Balance'#0''($balance#$2_coin_Coin'#0'(s))
}
function {:inline} $IsEqual'$2_coin_Coin'#0''(s1: $2_coin_Coin'#0', s2: $2_coin_Coin'#0'): bool {
    s1 == s2
}
var $2_coin_Coin'#0'_$memory: $Memory $2_coin_Coin'#0';

// fun coin::into_balance<#0> [baseline] at ./../sui/crates/sui-framework/sources/coin.move:74:5+146
procedure {:inline 1} $2_coin_into_balance'#0'(_$t0: $2_coin_Coin'#0') returns ($ret0: $2_balance_Balance'#0')
{
    // declare local variables
    var $t1: $2_balance_Balance'#0';
    var $t2: $2_object_UID;
    var $t3: $2_object_UID;
    var $t4: $2_balance_Balance'#0';
    var $t5: int;
    var $t0: $2_coin_Coin'#0';
    var $temp_0'$2_balance_Balance'#0'': $2_balance_Balance'#0';
    var $temp_0'$2_coin_Coin'#0'': $2_coin_Coin'#0';
    var $temp_0'$2_object_UID': $2_object_UID;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[coin]($t0) at ./../sui/crates/sui-framework/sources/coin.move:74:5+1
    assume {:print "$at(2,2325,2326)"} true;
    assume {:print "$track_local(14,7,0):", $t0} $t0 == $t0;

    // ($t3, $t4) := unpack coin::Coin<#0>($t0) at ./../sui/crates/sui-framework/sources/coin.move:75:13+20
    assume {:print "$at(2,2393,2413)"} true;
    $t3 := $id#$2_coin_Coin'#0'($t0);
    $t4 := $balance#$2_coin_Coin'#0'($t0);

    // trace_local[balance]($t4) at ./../sui/crates/sui-framework/sources/coin.move:75:24+7
    assume {:print "$track_local(14,7,1):", $t4} $t4 == $t4;

    // trace_local[id]($t3) at ./../sui/crates/sui-framework/sources/coin.move:75:20+2
    assume {:print "$track_local(14,7,2):", $t3} $t3 == $t3;

    // object::delete($t3) on_abort goto L2 with $t5 at ./../sui/crates/sui-framework/sources/coin.move:76:9+18
    assume {:print "$at(2,2430,2448)"} true;
    call $2_object_delete($t3);
    if ($abort_flag) {
        assume {:print "$at(2,2430,2448)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(14,7):", $t5} $t5 == $t5;
        goto L2;
    }

    // trace_return[0]($t4) at ./../sui/crates/sui-framework/sources/coin.move:77:9+7
    assume {:print "$at(2,2458,2465)"} true;
    assume {:print "$track_return(14,7,0):", $t4} $t4 == $t4;

    // label L1 at ./../sui/crates/sui-framework/sources/coin.move:78:5+1
    assume {:print "$at(2,2470,2471)"} true;
L1:

    // return $t4 at ./../sui/crates/sui-framework/sources/coin.move:78:5+1
    $ret0 := $t4;
    return;

    // label L2 at ./../sui/crates/sui-framework/sources/coin.move:78:5+1
L2:

    // abort($t5) at ./../sui/crates/sui-framework/sources/coin.move:78:5+1
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun coin::take<#0> [baseline] at ./../sui/crates/sui-framework/sources/coin.move:82:5+220
procedure {:inline 1} $2_coin_take'#0'(_$t0: $Mutation ($2_balance_Balance'#0'), _$t1: int, _$t2: $Mutation ($2_tx_context_TxContext)) returns ($ret0: $2_coin_Coin'#0', $ret1: $Mutation ($2_balance_Balance'#0'), $ret2: $Mutation ($2_tx_context_TxContext))
{
    // declare local variables
    var $t3: $2_object_UID;
    var $t4: int;
    var $t5: $2_balance_Balance'#0';
    var $t6: $2_coin_Coin'#0';
    var $t0: $Mutation ($2_balance_Balance'#0');
    var $t1: int;
    var $t2: $Mutation ($2_tx_context_TxContext);
    var $temp_0'$2_balance_Balance'#0'': $2_balance_Balance'#0';
    var $temp_0'$2_coin_Coin'#0'': $2_coin_Coin'#0';
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // bytecode translation starts here
    // trace_local[balance]($t0) at ./../sui/crates/sui-framework/sources/coin.move:82:5+1
    assume {:print "$at(2,2574,2575)"} true;
    $temp_0'$2_balance_Balance'#0'' := $Dereference($t0);
    assume {:print "$track_local(14,20,0):", $temp_0'$2_balance_Balance'#0''} $temp_0'$2_balance_Balance'#0'' == $temp_0'$2_balance_Balance'#0'';

    // trace_local[value]($t1) at ./../sui/crates/sui-framework/sources/coin.move:82:5+1
    assume {:print "$track_local(14,20,1):", $t1} $t1 == $t1;

    // trace_local[ctx]($t2) at ./../sui/crates/sui-framework/sources/coin.move:82:5+1
    $temp_0'$2_tx_context_TxContext' := $Dereference($t2);
    assume {:print "$track_local(14,20,2):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // $t3 := object::new($t2) on_abort goto L2 with $t4 at ./../sui/crates/sui-framework/sources/coin.move:86:17+16
    assume {:print "$at(2,2709,2725)"} true;
    call $t3,$t2 := $2_object_new($t2);
    if ($abort_flag) {
        assume {:print "$at(2,2709,2725)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(14,20):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t5 := balance::split<#0>($t0, $t1) on_abort goto L2 with $t4 at ./../sui/crates/sui-framework/sources/coin.move:87:22+30
    assume {:print "$at(2,2748,2778)"} true;
    call $t5,$t0 := $2_balance_split'#0'($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,2748,2778)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(14,20):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t6 := pack coin::Coin<#0>($t3, $t5) at ./../sui/crates/sui-framework/sources/coin.move:85:9+102
    assume {:print "$at(2,2686,2788)"} true;
    $t6 := $2_coin_Coin'#0'($t3, $t5);

    // trace_return[0]($t6) at ./../sui/crates/sui-framework/sources/coin.move:85:9+102
    assume {:print "$track_return(14,20,0):", $t6} $t6 == $t6;

    // trace_local[balance]($t0) at ./../sui/crates/sui-framework/sources/coin.move:85:9+102
    $temp_0'$2_balance_Balance'#0'' := $Dereference($t0);
    assume {:print "$track_local(14,20,0):", $temp_0'$2_balance_Balance'#0''} $temp_0'$2_balance_Balance'#0'' == $temp_0'$2_balance_Balance'#0'';

    // trace_local[ctx]($t2) at ./../sui/crates/sui-framework/sources/coin.move:85:9+102
    $temp_0'$2_tx_context_TxContext' := $Dereference($t2);
    assume {:print "$track_local(14,20,2):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // label L1 at ./../sui/crates/sui-framework/sources/coin.move:89:5+1
    assume {:print "$at(2,2793,2794)"} true;
L1:

    // return $t6 at ./../sui/crates/sui-framework/sources/coin.move:89:5+1
    $ret0 := $t6;
    $ret1 := $t0;
    $ret2 := $t2;
    return;

    // label L2 at ./../sui/crates/sui-framework/sources/coin.move:89:5+1
L2:

    // abort($t4) at ./../sui/crates/sui-framework/sources/coin.move:89:5+1
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// struct market::AdminCap at ./sources/market.move:27:5+70
type {:datatype} $0_market_AdminCap;
function {:constructor} $0_market_AdminCap($id: $2_object_UID, $market_id: $2_object_ID): $0_market_AdminCap;
function {:inline} $Update'$0_market_AdminCap'_id(s: $0_market_AdminCap, x: $2_object_UID): $0_market_AdminCap {
    $0_market_AdminCap(x, $market_id#$0_market_AdminCap(s))
}
function {:inline} $Update'$0_market_AdminCap'_market_id(s: $0_market_AdminCap, x: $2_object_ID): $0_market_AdminCap {
    $0_market_AdminCap($id#$0_market_AdminCap(s), x)
}
function $IsValid'$0_market_AdminCap'(s: $0_market_AdminCap): bool {
    $IsValid'$2_object_UID'($id#$0_market_AdminCap(s))
      && $IsValid'$2_object_ID'($market_id#$0_market_AdminCap(s))
}
function {:inline} $IsEqual'$0_market_AdminCap'(s1: $0_market_AdminCap, s2: $0_market_AdminCap): bool {
    s1 == s2
}
var $0_market_AdminCap_$memory: $Memory $0_market_AdminCap;

// struct market::BorrowRecord<#0, #1> at ./sources/market.move:39:5+150
type {:datatype} $0_market_BorrowRecord'#0_#1';
function {:constructor} $0_market_BorrowRecord'#0_#1'($id: $2_object_UID, $borrower: int, $col_amount: int, $bor_amount: int): $0_market_BorrowRecord'#0_#1';
function {:inline} $Update'$0_market_BorrowRecord'#0_#1''_id(s: $0_market_BorrowRecord'#0_#1', x: $2_object_UID): $0_market_BorrowRecord'#0_#1' {
    $0_market_BorrowRecord'#0_#1'(x, $borrower#$0_market_BorrowRecord'#0_#1'(s), $col_amount#$0_market_BorrowRecord'#0_#1'(s), $bor_amount#$0_market_BorrowRecord'#0_#1'(s))
}
function {:inline} $Update'$0_market_BorrowRecord'#0_#1''_borrower(s: $0_market_BorrowRecord'#0_#1', x: int): $0_market_BorrowRecord'#0_#1' {
    $0_market_BorrowRecord'#0_#1'($id#$0_market_BorrowRecord'#0_#1'(s), x, $col_amount#$0_market_BorrowRecord'#0_#1'(s), $bor_amount#$0_market_BorrowRecord'#0_#1'(s))
}
function {:inline} $Update'$0_market_BorrowRecord'#0_#1''_col_amount(s: $0_market_BorrowRecord'#0_#1', x: int): $0_market_BorrowRecord'#0_#1' {
    $0_market_BorrowRecord'#0_#1'($id#$0_market_BorrowRecord'#0_#1'(s), $borrower#$0_market_BorrowRecord'#0_#1'(s), x, $bor_amount#$0_market_BorrowRecord'#0_#1'(s))
}
function {:inline} $Update'$0_market_BorrowRecord'#0_#1''_bor_amount(s: $0_market_BorrowRecord'#0_#1', x: int): $0_market_BorrowRecord'#0_#1' {
    $0_market_BorrowRecord'#0_#1'($id#$0_market_BorrowRecord'#0_#1'(s), $borrower#$0_market_BorrowRecord'#0_#1'(s), $col_amount#$0_market_BorrowRecord'#0_#1'(s), x)
}
function $IsValid'$0_market_BorrowRecord'#0_#1''(s: $0_market_BorrowRecord'#0_#1'): bool {
    $IsValid'$2_object_UID'($id#$0_market_BorrowRecord'#0_#1'(s))
      && $IsValid'address'($borrower#$0_market_BorrowRecord'#0_#1'(s))
      && $IsValid'u64'($col_amount#$0_market_BorrowRecord'#0_#1'(s))
      && $IsValid'u64'($bor_amount#$0_market_BorrowRecord'#0_#1'(s))
}
function {:inline} $IsEqual'$0_market_BorrowRecord'#0_#1''(s1: $0_market_BorrowRecord'#0_#1', s2: $0_market_BorrowRecord'#0_#1'): bool {
    s1 == s2
}
var $0_market_BorrowRecord'#0_#1'_$memory: $Memory $0_market_BorrowRecord'#0_#1';

// struct market::ColData at ./sources/market.move:33:5+74
type {:datatype} $0_market_ColData;
function {:constructor} $0_market_ColData($gross: int, $utilized: int): $0_market_ColData;
function {:inline} $Update'$0_market_ColData'_gross(s: $0_market_ColData, x: int): $0_market_ColData {
    $0_market_ColData(x, $utilized#$0_market_ColData(s))
}
function {:inline} $Update'$0_market_ColData'_utilized(s: $0_market_ColData, x: int): $0_market_ColData {
    $0_market_ColData($gross#$0_market_ColData(s), x)
}
function $IsValid'$0_market_ColData'(s: $0_market_ColData): bool {
    $IsValid'u64'($gross#$0_market_ColData(s))
      && $IsValid'u64'($utilized#$0_market_ColData(s))
}
function {:inline} $IsEqual'$0_market_ColData'(s1: $0_market_ColData, s2: $0_market_ColData): bool {
    s1 == s2
}

// struct market::Market at ./sources/market.move:15:5+119
type {:datatype} $0_market_Market;
function {:constructor} $0_market_Market($id: $2_object_UID, $submarket_ids: $2_vec_set_VecSet'$2_object_ID', $borrow_record_ids: Vec ($2_object_ID)): $0_market_Market;
function {:inline} $Update'$0_market_Market'_id(s: $0_market_Market, x: $2_object_UID): $0_market_Market {
    $0_market_Market(x, $submarket_ids#$0_market_Market(s), $borrow_record_ids#$0_market_Market(s))
}
function {:inline} $Update'$0_market_Market'_submarket_ids(s: $0_market_Market, x: $2_vec_set_VecSet'$2_object_ID'): $0_market_Market {
    $0_market_Market($id#$0_market_Market(s), x, $borrow_record_ids#$0_market_Market(s))
}
function {:inline} $Update'$0_market_Market'_borrow_record_ids(s: $0_market_Market, x: Vec ($2_object_ID)): $0_market_Market {
    $0_market_Market($id#$0_market_Market(s), $submarket_ids#$0_market_Market(s), x)
}
function $IsValid'$0_market_Market'(s: $0_market_Market): bool {
    $IsValid'$2_object_UID'($id#$0_market_Market(s))
      && $IsValid'$2_vec_set_VecSet'$2_object_ID''($submarket_ids#$0_market_Market(s))
      && $IsValid'vec'$2_object_ID''($borrow_record_ids#$0_market_Market(s))
}
function {:inline} $IsEqual'$0_market_Market'(s1: $0_market_Market, s2: $0_market_Market): bool {
    $IsEqual'$2_object_UID'($id#$0_market_Market(s1), $id#$0_market_Market(s2))
    && $IsEqual'$2_vec_set_VecSet'$2_object_ID''($submarket_ids#$0_market_Market(s1), $submarket_ids#$0_market_Market(s2))
    && $IsEqual'vec'$2_object_ID''($borrow_record_ids#$0_market_Market(s1), $borrow_record_ids#$0_market_Market(s2))}
var $0_market_Market_$memory: $Memory $0_market_Market;

// struct market::SubMarket<#0> at ./sources/market.move:21:5+135
type {:datatype} $0_market_SubMarket'#0';
function {:constructor} $0_market_SubMarket'#0'($id: $2_object_UID, $balance: $2_balance_Balance'#0', $collaterals: $2_vec_map_VecMap'address_$0_market_ColData'): $0_market_SubMarket'#0';
function {:inline} $Update'$0_market_SubMarket'#0''_id(s: $0_market_SubMarket'#0', x: $2_object_UID): $0_market_SubMarket'#0' {
    $0_market_SubMarket'#0'(x, $balance#$0_market_SubMarket'#0'(s), $collaterals#$0_market_SubMarket'#0'(s))
}
function {:inline} $Update'$0_market_SubMarket'#0''_balance(s: $0_market_SubMarket'#0', x: $2_balance_Balance'#0'): $0_market_SubMarket'#0' {
    $0_market_SubMarket'#0'($id#$0_market_SubMarket'#0'(s), x, $collaterals#$0_market_SubMarket'#0'(s))
}
function {:inline} $Update'$0_market_SubMarket'#0''_collaterals(s: $0_market_SubMarket'#0', x: $2_vec_map_VecMap'address_$0_market_ColData'): $0_market_SubMarket'#0' {
    $0_market_SubMarket'#0'($id#$0_market_SubMarket'#0'(s), $balance#$0_market_SubMarket'#0'(s), x)
}
function $IsValid'$0_market_SubMarket'#0''(s: $0_market_SubMarket'#0'): bool {
    $IsValid'$2_object_UID'($id#$0_market_SubMarket'#0'(s))
      && $IsValid'$2_balance_Balance'#0''($balance#$0_market_SubMarket'#0'(s))
      && $IsValid'$2_vec_map_VecMap'address_$0_market_ColData''($collaterals#$0_market_SubMarket'#0'(s))
}
function {:inline} $IsEqual'$0_market_SubMarket'#0''(s1: $0_market_SubMarket'#0', s2: $0_market_SubMarket'#0'): bool {
    $IsEqual'$2_object_UID'($id#$0_market_SubMarket'#0'(s1), $id#$0_market_SubMarket'#0'(s2))
    && $IsEqual'$2_balance_Balance'#0''($balance#$0_market_SubMarket'#0'(s1), $balance#$0_market_SubMarket'#0'(s2))
    && $IsEqual'$2_vec_map_VecMap'address_$0_market_ColData''($collaterals#$0_market_SubMarket'#0'(s1), $collaterals#$0_market_SubMarket'#0'(s2))}
var $0_market_SubMarket'#0'_$memory: $Memory $0_market_SubMarket'#0';

// struct market::SubMarket<#1> at ./sources/market.move:21:5+135
type {:datatype} $0_market_SubMarket'#1';
function {:constructor} $0_market_SubMarket'#1'($id: $2_object_UID, $balance: $2_balance_Balance'#1', $collaterals: $2_vec_map_VecMap'address_$0_market_ColData'): $0_market_SubMarket'#1';
function {:inline} $Update'$0_market_SubMarket'#1''_id(s: $0_market_SubMarket'#1', x: $2_object_UID): $0_market_SubMarket'#1' {
    $0_market_SubMarket'#1'(x, $balance#$0_market_SubMarket'#1'(s), $collaterals#$0_market_SubMarket'#1'(s))
}
function {:inline} $Update'$0_market_SubMarket'#1''_balance(s: $0_market_SubMarket'#1', x: $2_balance_Balance'#1'): $0_market_SubMarket'#1' {
    $0_market_SubMarket'#1'($id#$0_market_SubMarket'#1'(s), x, $collaterals#$0_market_SubMarket'#1'(s))
}
function {:inline} $Update'$0_market_SubMarket'#1''_collaterals(s: $0_market_SubMarket'#1', x: $2_vec_map_VecMap'address_$0_market_ColData'): $0_market_SubMarket'#1' {
    $0_market_SubMarket'#1'($id#$0_market_SubMarket'#1'(s), $balance#$0_market_SubMarket'#1'(s), x)
}
function $IsValid'$0_market_SubMarket'#1''(s: $0_market_SubMarket'#1'): bool {
    $IsValid'$2_object_UID'($id#$0_market_SubMarket'#1'(s))
      && $IsValid'$2_balance_Balance'#1''($balance#$0_market_SubMarket'#1'(s))
      && $IsValid'$2_vec_map_VecMap'address_$0_market_ColData''($collaterals#$0_market_SubMarket'#1'(s))
}
function {:inline} $IsEqual'$0_market_SubMarket'#1''(s1: $0_market_SubMarket'#1', s2: $0_market_SubMarket'#1'): bool {
    $IsEqual'$2_object_UID'($id#$0_market_SubMarket'#1'(s1), $id#$0_market_SubMarket'#1'(s2))
    && $IsEqual'$2_balance_Balance'#1''($balance#$0_market_SubMarket'#1'(s1), $balance#$0_market_SubMarket'#1'(s2))
    && $IsEqual'$2_vec_map_VecMap'address_$0_market_ColData''($collaterals#$0_market_SubMarket'#1'(s1), $collaterals#$0_market_SubMarket'#1'(s2))}
var $0_market_SubMarket'#1'_$memory: $Memory $0_market_SubMarket'#1';

// fun market::borrow [verification] at ./sources/market.move:101:5+1677
procedure {:timeLimit 40} $0_market_borrow$verify(_$t0: int, _$t1: int, _$t2: $Mutation ($0_market_SubMarket'#0'), _$t3: $Mutation ($0_market_SubMarket'#1'), _$t4: $Mutation ($0_market_Market), _$t5: $Mutation ($2_tx_context_TxContext)) returns ($ret0: $2_coin_Coin'#0', $ret1: $Mutation ($0_market_SubMarket'#0'), $ret2: $Mutation ($0_market_SubMarket'#1'), $ret3: $Mutation ($0_market_Market), $ret4: $Mutation ($2_tx_context_TxContext))
{
    // declare local variables
    var $t6: $Mutation ($0_market_Market);
    var $t7: $Mutation ($0_market_SubMarket'#0');
    var $t8: $Mutation ($0_market_Market);
    var $t9: $Mutation ($0_market_SubMarket'#1');
    var $t10: int;
    var $t11: int;
    var $t12: $Mutation ($0_market_SubMarket'#1');
    var $t13: int;
    var $t14: $Mutation ($2_vec_map_VecMap'address_$0_market_ColData');
    var $t15: $0_market_BorrowRecord'#0_#1';
    var $t16: int;
    var $t17: int;
    var $t18: $0_market_Market;
    var $t19: $0_market_SubMarket'#0';
    var $t20: int;
    var $t21: $0_market_Market;
    var $t22: $0_market_SubMarket'#1';
    var $t23: $2_balance_Balance'#0';
    var $t24: int;
    var $t25: bool;
    var $t26: int;
    var $t27: int;
    var $t28: $2_tx_context_TxContext;
    var $t29: int;
    var $t30: $0_market_SubMarket'#1';
    var $t31: int;
    var $t32: bool;
    var $t33: int;
    var $t34: int;
    var $t35: int;
    var $t36: bool;
    var $t37: int;
    var $t38: int;
    var $t39: $Mutation ($2_vec_map_VecMap'address_$0_market_ColData');
    var $t40: $2_tx_context_TxContext;
    var $t41: int;
    var $t42: $2_object_UID;
    var $t43: $2_tx_context_TxContext;
    var $t44: int;
    var $t45: $0_market_BorrowRecord'#0_#1';
    var $t46: $Mutation (Vec ($2_object_ID));
    var $t47: $2_object_UID;
    var $t48: $2_object_ID;
    var $t49: $Mutation ($2_balance_Balance'#0');
    var $t50: $2_coin_Coin'#0';
    var $t0: int;
    var $t1: int;
    var $t2: $Mutation ($0_market_SubMarket'#0');
    var $t3: $Mutation ($0_market_SubMarket'#1');
    var $t4: $Mutation ($0_market_Market);
    var $t5: $Mutation ($2_tx_context_TxContext);
    var $temp_0'$0_market_BorrowRecord'#0_#1'': $0_market_BorrowRecord'#0_#1';
    var $temp_0'$0_market_Market': $0_market_Market;
    var $temp_0'$0_market_SubMarket'#0'': $0_market_SubMarket'#0';
    var $temp_0'$0_market_SubMarket'#1'': $0_market_SubMarket'#1';
    var $temp_0'$2_coin_Coin'#0'': $2_coin_Coin'#0';
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;
    $t3 := _$t3;
    $t4 := _$t4;
    $t5 := _$t5;
    assume IsEmptyVec(p#$Mutation($t6));
    assume IsEmptyVec(p#$Mutation($t7));
    assume IsEmptyVec(p#$Mutation($t8));
    assume IsEmptyVec(p#$Mutation($t9));
    assume IsEmptyVec(p#$Mutation($t12));
    assume IsEmptyVec(p#$Mutation($t14));
    assume IsEmptyVec(p#$Mutation($t39));
    assume IsEmptyVec(p#$Mutation($t46));
    assume IsEmptyVec(p#$Mutation($t49));

    // verification entrypoint assumptions
    call $InitVerification();
    assume l#$Mutation($t2) == $Param(2);
    assume l#$Mutation($t3) == $Param(3);
    assume l#$Mutation($t4) == $Param(4);
    assume l#$Mutation($t5) == $Param(5);

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/market.move:101:5+1
    assume {:print "$at(20,3334,3335)"} true;
    assume $IsValid'u64'($t0);

    // assume WellFormed($t1) at ./sources/market.move:101:5+1
    assume $IsValid'u64'($t1);

    // assume WellFormed($t2) at ./sources/market.move:101:5+1
    assume $IsValid'$0_market_SubMarket'#0''($Dereference($t2));

    // assume WellFormed($t3) at ./sources/market.move:101:5+1
    assume $IsValid'$0_market_SubMarket'#1''($Dereference($t3));

    // assume WellFormed($t4) at ./sources/market.move:101:5+1
    assume $IsValid'$0_market_Market'($Dereference($t4));

    // assume WellFormed($t5) at ./sources/market.move:101:5+1
    assume $IsValid'$2_tx_context_TxContext'($Dereference($t5));

    // trace_local[bor_amount]($t0) at ./sources/market.move:101:5+1
    assume {:print "$track_local(15,1,0):", $t0} $t0 == $t0;

    // trace_local[col_amount]($t1) at ./sources/market.move:101:5+1
    assume {:print "$track_local(15,1,1):", $t1} $t1 == $t1;

    // trace_local[bor_market]($t2) at ./sources/market.move:101:5+1
    $temp_0'$0_market_SubMarket'#0'' := $Dereference($t2);
    assume {:print "$track_local(15,1,2):", $temp_0'$0_market_SubMarket'#0''} $temp_0'$0_market_SubMarket'#0'' == $temp_0'$0_market_SubMarket'#0'';

    // trace_local[col_market]($t3) at ./sources/market.move:101:5+1
    $temp_0'$0_market_SubMarket'#1'' := $Dereference($t3);
    assume {:print "$track_local(15,1,3):", $temp_0'$0_market_SubMarket'#1''} $temp_0'$0_market_SubMarket'#1'' == $temp_0'$0_market_SubMarket'#1'';

    // trace_local[market]($t4) at ./sources/market.move:101:5+1
    $temp_0'$0_market_Market' := $Dereference($t4);
    assume {:print "$track_local(15,1,4):", $temp_0'$0_market_Market'} $temp_0'$0_market_Market' == $temp_0'$0_market_Market';

    // trace_local[ctx]($t5) at ./sources/market.move:101:5+1
    $temp_0'$2_tx_context_TxContext' := $Dereference($t5);
    assume {:print "$track_local(15,1,5):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // $t18 := read_ref($t4) at ./sources/market.move:106:20+20
    assume {:print "$at(20,3601,3621)"} true;
    $t18 := $Dereference($t4);

    // $t19 := read_ref($t2) at ./sources/market.move:106:20+20
    $t19 := $Dereference($t2);

    // market::check_child<#0>($t18, $t19) on_abort goto L7 with $t20 at ./sources/market.move:106:9+31
    call $0_market_check_child'#0'($t18, $t19);
    if ($abort_flag) {
        assume {:print "$at(20,3590,3621)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(15,1):", $t20} $t20 == $t20;
        goto L7;
    }

    // $t21 := read_ref($t4) at ./sources/market.move:107:20+20
    assume {:print "$at(20,3642,3662)"} true;
    $t21 := $Dereference($t4);

    // $t22 := read_ref($t3) at ./sources/market.move:107:20+20
    $t22 := $Dereference($t3);

    // market::check_child<#1>($t21, $t22) on_abort goto L7 with $t20 at ./sources/market.move:107:9+31
    call $0_market_check_child'#1'($t21, $t22);
    if ($abort_flag) {
        assume {:print "$at(20,3631,3662)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(15,1):", $t20} $t20 == $t20;
        goto L7;
    }

    // $t23 := get_field<market::SubMarket<#0>>.balance($t2) at ./sources/market.move:110:32+19
    assume {:print "$at(20,3748,3767)"} true;
    $t23 := $balance#$0_market_SubMarket'#0'($Dereference($t2));

    // $t24 := balance::value<#0>($t23) on_abort goto L7 with $t20 at ./sources/market.move:110:17+35
    call $t24 := $2_balance_value'#0'($t23);
    if ($abort_flag) {
        assume {:print "$at(20,3733,3768)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(15,1):", $t20} $t20 == $t20;
        goto L7;
    }

    // $t25 := >=($t24, $t0) at ./sources/market.move:110:53+2
    call $t25 := $Ge($t24, $t0);

    // if ($t25) goto L0 else goto L1 at ./sources/market.move:110:9+99
    if ($t25) { goto L0; } else { goto L1; }

    // label L1 at ./sources/market.move:110:9+99
L1:

    // destroy($t4) at ./sources/market.move:110:9+99

    // destroy($t5) at ./sources/market.move:110:9+99

    // destroy($t3) at ./sources/market.move:110:9+99

    // destroy($t2) at ./sources/market.move:110:9+99

    // $t26 := 5 at ./sources/market.move:110:93+13
    $t26 := 5;
    assume $IsValid'u64'($t26);

    // $t27 := opaque begin: errors::invalid_argument($t26) at ./sources/market.move:110:68+39

    // assume WellFormed($t27) at ./sources/market.move:110:68+39
    assume $IsValid'u64'($t27);

    // assume Eq<u64>($t27, 7) at ./sources/market.move:110:68+39
    assume $IsEqual'u64'($t27, 7);

    // $t27 := opaque end: errors::invalid_argument($t26) at ./sources/market.move:110:68+39

    // trace_abort($t27) at ./sources/market.move:110:9+99
    assume {:print "$at(20,3725,3824)"} true;
    assume {:print "$track_abort(15,1):", $t27} $t27 == $t27;

    // $t20 := move($t27) at ./sources/market.move:110:9+99
    $t20 := $t27;

    // goto L7 at ./sources/market.move:110:9+99
    goto L7;

    // label L0 at ./sources/market.move:112:61+3
    assume {:print "$at(20,3887,3890)"} true;
L0:

    // $t28 := read_ref($t5) at ./sources/market.move:112:61+3
    $t28 := $Dereference($t5);

    // $t29 := tx_context::sender($t28) on_abort goto L7 with $t20 at ./sources/market.move:112:42+23
    call $t29 := $2_tx_context_sender($t28);
    if ($abort_flag) {
        assume {:print "$at(20,3868,3891)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(15,1):", $t20} $t20 == $t20;
        goto L7;
    }

    // $t30 := read_ref($t3) at ./sources/market.move:112:40+38
    $t30 := $Dereference($t3);

    // $t31 := market::get_unused_col<#1>($t29, $t30) on_abort goto L7 with $t20 at ./sources/market.move:112:26+52
    call $t31 := $0_market_get_unused_col'#1'($t29, $t30);
    if ($abort_flag) {
        assume {:print "$at(20,3852,3904)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(15,1):", $t20} $t20 == $t20;
        goto L7;
    }

    // trace_local[unused_col]($t31) at ./sources/market.move:112:13+10
    assume {:print "$track_local(15,1,17):", $t31} $t31 == $t31;

    // $t32 := >=($t31, $t1) at ./sources/market.move:114:28+2
    assume {:print "$at(20,3987,3989)"} true;
    call $t32 := $Ge($t31, $t1);

    // if ($t32) goto L2 else goto L3 at ./sources/market.move:114:9+78
    if ($t32) { goto L2; } else { goto L3; }

    // label L3 at ./sources/market.move:114:9+78
L3:

    // destroy($t4) at ./sources/market.move:114:9+78

    // destroy($t5) at ./sources/market.move:114:9+78

    // destroy($t3) at ./sources/market.move:114:9+78

    // destroy($t2) at ./sources/market.move:114:9+78

    // $t33 := 6 at ./sources/market.move:114:68+17
    $t33 := 6;
    assume $IsValid'u64'($t33);

    // $t34 := opaque begin: errors::invalid_argument($t33) at ./sources/market.move:114:43+43

    // assume WellFormed($t34) at ./sources/market.move:114:43+43
    assume $IsValid'u64'($t34);

    // assume Eq<u64>($t34, 7) at ./sources/market.move:114:43+43
    assume $IsEqual'u64'($t34, 7);

    // $t34 := opaque end: errors::invalid_argument($t33) at ./sources/market.move:114:43+43

    // trace_abort($t34) at ./sources/market.move:114:9+78
    assume {:print "$at(20,3968,4046)"} true;
    assume {:print "$track_abort(15,1):", $t34} $t34 == $t34;

    // $t20 := move($t34) at ./sources/market.move:114:9+78
    $t20 := $t34;

    // goto L7 at ./sources/market.move:114:9+78
    goto L7;

    // label L2 at ./sources/market.move:117:81+10
    assume {:print "$at(20,4222,4232)"} true;
L2:

    // $t35 := calculator::required_collateral_amount<#0, #1>($t0) on_abort goto L7 with $t20 at ./sources/market.move:117:36+56
    call $t35 := $0_calculator_required_collateral_amount'#0_#1'($t0);
    if ($abort_flag) {
        assume {:print "$at(20,4177,4233)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(15,1):", $t20} $t20 == $t20;
        goto L7;
    }

    // trace_local[minimum_required_col]($t35) at ./sources/market.move:117:13+20
    assume {:print "$track_local(15,1,16):", $t35} $t35 == $t35;

    // $t36 := >=($t1, $t35) at ./sources/market.move:118:28+2
    assume {:print "$at(20,4262,4264)"} true;
    call $t36 := $Ge($t1, $t35);

    // if ($t36) goto L4 else goto L5 at ./sources/market.move:118:9+91
    if ($t36) { goto L4; } else { goto L5; }

    // label L5 at ./sources/market.move:118:9+91
L5:

    // destroy($t4) at ./sources/market.move:118:9+91

    // destroy($t5) at ./sources/market.move:118:9+91

    // destroy($t3) at ./sources/market.move:118:9+91

    // destroy($t2) at ./sources/market.move:118:9+91

    // $t37 := 7 at ./sources/market.move:118:78+20
    $t37 := 7;
    assume $IsValid'u64'($t37);

    // $t38 := opaque begin: errors::invalid_argument($t37) at ./sources/market.move:118:53+46

    // assume WellFormed($t38) at ./sources/market.move:118:53+46
    assume $IsValid'u64'($t38);

    // assume Eq<u64>($t38, 7) at ./sources/market.move:118:53+46
    assume $IsEqual'u64'($t38, 7);

    // $t38 := opaque end: errors::invalid_argument($t37) at ./sources/market.move:118:53+46

    // trace_abort($t38) at ./sources/market.move:118:9+91
    assume {:print "$at(20,4243,4334)"} true;
    assume {:print "$track_abort(15,1):", $t38} $t38 == $t38;

    // $t20 := move($t38) at ./sources/market.move:118:9+91
    $t20 := $t38;

    // goto L7 at ./sources/market.move:118:9+91
    goto L7;

    // label L4 at ./sources/market.move:120:37+10
    assume {:print "$at(20,4373,4383)"} true;
L4:

    // $t39 := borrow_field<market::SubMarket<#1>>.collaterals($t3) at ./sources/market.move:120:32+27
    $t39 := $ChildMutation($t3, 2, $collaterals#$0_market_SubMarket'#1'($Dereference($t3)));

    // $t40 := read_ref($t5) at ./sources/market.move:120:81+3
    $t40 := $Dereference($t5);

    // $t41 := tx_context::sender($t40) on_abort goto L7 with $t20 at ./sources/market.move:120:62+23
    call $t41 := $2_tx_context_sender($t40);
    if ($abort_flag) {
        assume {:print "$at(20,4398,4421)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(15,1):", $t20} $t20 == $t20;
        goto L7;
    }

    // market::record_new_utilization($t39, $t41, $t1) on_abort goto L7 with $t20 at ./sources/market.move:120:9+89
    call $t39 := $0_market_record_new_utilization($t39, $t41, $t1);
    if ($abort_flag) {
        assume {:print "$at(20,4345,4434)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(15,1):", $t20} $t20 == $t20;
        goto L7;
    }

    // write_back[Reference($t3).collaterals (vec_map::VecMap<address, market::ColData>)]($t39) at ./sources/market.move:120:9+89
    $t3 := $UpdateMutation($t3, $Update'$0_market_SubMarket'#1''_collaterals($Dereference($t3), $Dereference($t39)));

    // trace_local[col_market]($t3) at ./sources/market.move:120:9+89
    $temp_0'$0_market_SubMarket'#1'' := $Dereference($t3);
    assume {:print "$track_local(15,1,3):", $temp_0'$0_market_SubMarket'#1''} $temp_0'$0_market_SubMarket'#1'' == $temp_0'$0_market_SubMarket'#1'';

    // $t42 := object::new($t5) on_abort goto L7 with $t20 at ./sources/market.move:124:17+16
    assume {:print "$at(20,4556,4572)"} true;
    call $t42,$t5 := $2_object_new($t5);
    if ($abort_flag) {
        assume {:print "$at(20,4556,4572)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(15,1):", $t20} $t20 == $t20;
        goto L7;
    }

    // $t43 := read_ref($t5) at ./sources/market.move:125:42+3
    assume {:print "$at(20,4615,4618)"} true;
    $t43 := $Dereference($t5);

    // $t44 := tx_context::sender($t43) on_abort goto L7 with $t20 at ./sources/market.move:125:23+23
    call $t44 := $2_tx_context_sender($t43);
    if ($abort_flag) {
        assume {:print "$at(20,4596,4619)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(15,1):", $t20} $t20 == $t20;
        goto L7;
    }

    // $t45 := pack market::BorrowRecord<#0, #1>($t42, $t44, $t1, $t0) at ./sources/market.move:123:29+182
    assume {:print "$at(20,4519,4701)"} true;
    $t45 := $0_market_BorrowRecord'#0_#1'($t42, $t44, $t1, $t0);

    // trace_local[borrow_record]($t45) at ./sources/market.move:123:13+13
    assume {:print "$track_local(15,1,15):", $t45} $t45 == $t45;

    // $t46 := borrow_field<market::Market>.borrow_record_ids($t4) at ./sources/market.move:131:27+29
    assume {:print "$at(20,4810,4839)"} true;
    $t46 := $ChildMutation($t4, 2, $borrow_record_ids#$0_market_Market($Dereference($t4)));

    // $t47 := get_field<market::BorrowRecord<#0, #1>>.id($t45) at ./sources/market.move:131:79+17
    $t47 := $id#$0_market_BorrowRecord'#0_#1'($t45);

    // $t48 := object::uid_to_inner($t47) on_abort goto L7 with $t20 at ./sources/market.move:131:58+39
    call $t48 := $2_object_uid_to_inner($t47);
    if ($abort_flag) {
        assume {:print "$at(20,4841,4880)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(15,1):", $t20} $t20 == $t20;
        goto L7;
    }

    // vector::push_back<object::ID>($t46, $t48) on_abort goto L7 with $t20 at ./sources/market.move:131:9+89
    call $t46 := $1_vector_push_back'$2_object_ID'($t46, $t48);
    if ($abort_flag) {
        assume {:print "$at(20,4792,4881)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(15,1):", $t20} $t20 == $t20;
        goto L7;
    }

    // write_back[Reference($t4).borrow_record_ids (vector<object::ID>)]($t46) at ./sources/market.move:131:9+89
    $t4 := $UpdateMutation($t4, $Update'$0_market_Market'_borrow_record_ids($Dereference($t4), $Dereference($t46)));

    // trace_local[market]($t4) at ./sources/market.move:131:9+89
    $temp_0'$0_market_Market' := $Dereference($t4);
    assume {:print "$track_local(15,1,4):", $temp_0'$0_market_Market'} $temp_0'$0_market_Market' == $temp_0'$0_market_Market';

    // transfer::transfer_to_object<market::BorrowRecord<#0, #1>, market::Market>($t45, $t4) on_abort goto L7 with $t20 at ./sources/market.move:132:9+51
    assume {:print "$at(20,4891,4942)"} true;
    call $t4 := $2_transfer_transfer_to_object'$0_market_BorrowRecord'#0_#1'_$0_market_Market'($t45, $t4);
    if ($abort_flag) {
        assume {:print "$at(20,4891,4942)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(15,1):", $t20} $t20 == $t20;
        goto L7;
    }

    // $t49 := borrow_field<market::SubMarket<#0>>.balance($t2) at ./sources/market.move:134:20+23
    assume {:print "$at(20,4964,4987)"} true;
    $t49 := $ChildMutation($t2, 1, $balance#$0_market_SubMarket'#0'($Dereference($t2)));

    // $t50 := coin::take<#0>($t49, $t1, $t5) on_abort goto L7 with $t20 at ./sources/market.move:134:9+52
    call $t50,$t49,$t5 := $2_coin_take'#0'($t49, $t1, $t5);
    if ($abort_flag) {
        assume {:print "$at(20,4953,5005)"} true;
        $t20 := $abort_code;
        assume {:print "$track_abort(15,1):", $t20} $t20 == $t20;
        goto L7;
    }

    // write_back[Reference($t2).balance (balance::Balance<#0>)]($t49) at ./sources/market.move:134:9+52
    $t2 := $UpdateMutation($t2, $Update'$0_market_SubMarket'#0''_balance($Dereference($t2), $Dereference($t49)));

    // trace_local[bor_market]($t2) at ./sources/market.move:134:9+52
    $temp_0'$0_market_SubMarket'#0'' := $Dereference($t2);
    assume {:print "$track_local(15,1,2):", $temp_0'$0_market_SubMarket'#0''} $temp_0'$0_market_SubMarket'#0'' == $temp_0'$0_market_SubMarket'#0'';

    // trace_return[0]($t50) at ./sources/market.move:134:9+52
    assume {:print "$track_return(15,1,0):", $t50} $t50 == $t50;

    // trace_local[bor_market]($t2) at ./sources/market.move:134:9+52
    $temp_0'$0_market_SubMarket'#0'' := $Dereference($t2);
    assume {:print "$track_local(15,1,2):", $temp_0'$0_market_SubMarket'#0''} $temp_0'$0_market_SubMarket'#0'' == $temp_0'$0_market_SubMarket'#0'';

    // trace_local[col_market]($t3) at ./sources/market.move:134:9+52
    $temp_0'$0_market_SubMarket'#1'' := $Dereference($t3);
    assume {:print "$track_local(15,1,3):", $temp_0'$0_market_SubMarket'#1''} $temp_0'$0_market_SubMarket'#1'' == $temp_0'$0_market_SubMarket'#1'';

    // trace_local[market]($t4) at ./sources/market.move:134:9+52
    $temp_0'$0_market_Market' := $Dereference($t4);
    assume {:print "$track_local(15,1,4):", $temp_0'$0_market_Market'} $temp_0'$0_market_Market' == $temp_0'$0_market_Market';

    // trace_local[ctx]($t5) at ./sources/market.move:134:9+52
    $temp_0'$2_tx_context_TxContext' := $Dereference($t5);
    assume {:print "$track_local(15,1,5):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // label L6 at ./sources/market.move:135:5+1
    assume {:print "$at(20,5010,5011)"} true;
L6:

    // return $t50 at ./sources/market.move:135:5+1
    $ret0 := $t50;
    $ret1 := $t2;
    $ret2 := $t3;
    $ret3 := $t4;
    $ret4 := $t5;
    return;

    // label L7 at ./sources/market.move:135:5+1
L7:

    // abort($t20) at ./sources/market.move:135:5+1
    $abort_code := $t20;
    $abort_flag := true;
    return;

}

// fun market::add_col_value [baseline] at ./sources/market.move:151:5+396
procedure {:inline 1} $0_market_add_col_value(_$t0: $Mutation ($2_vec_map_VecMap'address_$0_market_ColData'), _$t1: int, _$t2: int) returns ($ret0: $Mutation ($2_vec_map_VecMap'address_$0_market_ColData'))
{
    // declare local variables
    var $t3: $Mutation ($2_vec_map_VecMap'address_$0_market_ColData');
    var $t4: int;
    var $t5: $0_market_ColData;
    var $t6: $Mutation ($0_market_ColData);
    var $t7: $2_vec_map_VecMap'address_$0_market_ColData';
    var $t8: bool;
    var $t9: int;
    var $t10: bool;
    var $t11: int;
    var $t12: int;
    var $t13: $0_market_ColData;
    var $t14: $Mutation ($0_market_ColData);
    var $t15: int;
    var $t16: int;
    var $t17: $Mutation (int);
    var $t0: $Mutation ($2_vec_map_VecMap'address_$0_market_ColData');
    var $t1: int;
    var $t2: int;
    var $temp_0'$0_market_ColData': $0_market_ColData;
    var $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'': $2_vec_map_VecMap'address_$0_market_ColData';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;
    assume IsEmptyVec(p#$Mutation($t3));
    assume IsEmptyVec(p#$Mutation($t6));
    assume IsEmptyVec(p#$Mutation($t14));
    assume IsEmptyVec(p#$Mutation($t17));

    // bytecode translation starts here
    // trace_local[collaterals]($t0) at ./sources/market.move:151:5+1
    assume {:print "$at(20,5594,5595)"} true;
    $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' := $Dereference($t0);
    assume {:print "$track_local(15,0,0):", $temp_0'$2_vec_map_VecMap'address_$0_market_ColData''} $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' == $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'';

    // trace_local[sender]($t1) at ./sources/market.move:151:5+1
    assume {:print "$track_local(15,0,1):", $t1} $t1 == $t1;

    // trace_local[value]($t2) at ./sources/market.move:151:5+1
    assume {:print "$track_local(15,0,2):", $t2} $t2 == $t2;

    // $t7 := read_ref($t0) at ./sources/market.move:152:30+22
    assume {:print "$at(20,5716,5738)"} true;
    $t7 := $Dereference($t0);

    // $t8 := vec_map::contains<address, market::ColData>($t7, $t1) on_abort goto L4 with $t9 at ./sources/market.move:152:13+39
    call $t8 := $2_vec_map_contains'address_$0_market_ColData'($t7, $t1);
    if ($abort_flag) {
        assume {:print "$at(20,5699,5738)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(15,0):", $t9} $t9 == $t9;
        goto L4;
    }

    // $t10 := !($t8) at ./sources/market.move:152:12+1
    call $t10 := $Not($t8);

    // if ($t10) goto L0 else goto L2 at ./sources/market.move:152:9+175
    if ($t10) { goto L0; } else { goto L2; }

    // label L0 at ./sources/market.move:154:29+11
    assume {:print "$at(20,5829,5840)"} true;
L0:

    // $t11 := 0 at ./sources/market.move:153:43+1
    assume {:print "$at(20,5784,5785)"} true;
    $t11 := 0;
    assume $IsValid'u64'($t11);

    // $t12 := 0 at ./sources/market.move:153:56+1
    $t12 := 0;
    assume $IsValid'u64'($t12);

    // $t13 := pack market::ColData($t11, $t12) at ./sources/market.move:153:28+30
    $t13 := $0_market_ColData($t11, $t12);

    // vec_map::insert<address, market::ColData>($t0, $t1, $t13) on_abort goto L4 with $t9 at ./sources/market.move:154:13+46
    assume {:print "$at(20,5813,5859)"} true;
    call $t0 := $2_vec_map_insert'address_$0_market_ColData'($t0, $t1, $t13);
    if ($abort_flag) {
        assume {:print "$at(20,5813,5859)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(15,0):", $t9} $t9 == $t9;
        goto L4;
    }

    // label L2 at ./sources/market.move:157:41+11
    assume {:print "$at(20,5913,5924)"} true;
L2:

    // $t14 := vec_map::get_mut<address, market::ColData>($t0, $t1) on_abort goto L4 with $t9 at ./sources/market.move:157:24+38
    call $t14,$t0 := $2_vec_map_get_mut'address_$0_market_ColData'($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(20,5896,5934)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(15,0):", $t9} $t9 == $t9;
        goto L4;
    }

    // trace_local[col_data#3]($t14) at ./sources/market.move:157:13+8
    $temp_0'$0_market_ColData' := $Dereference($t14);
    assume {:print "$track_local(15,0,6):", $temp_0'$0_market_ColData'} $temp_0'$0_market_ColData' == $temp_0'$0_market_ColData';

    // $t15 := get_field<market::ColData>.gross($t14) at ./sources/market.move:158:26+14
    assume {:print "$at(20,5961,5975)"} true;
    $t15 := $gross#$0_market_ColData($Dereference($t14));

    // $t16 := +($t15, $t2) on_abort goto L4 with $t9 at ./sources/market.move:158:41+1
    call $t16 := $AddU64($t15, $t2);
    if ($abort_flag) {
        assume {:print "$at(20,5976,5977)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(15,0):", $t9} $t9 == $t9;
        goto L4;
    }

    // $t17 := borrow_field<market::ColData>.gross($t14) at ./sources/market.move:158:9+14
    $t17 := $ChildMutation($t14, 0, $gross#$0_market_ColData($Dereference($t14)));

    // write_ref($t17, $t16) at ./sources/market.move:158:9+39
    $t17 := $UpdateMutation($t17, $t16);

    // write_back[Reference($t14).gross (u64)]($t17) at ./sources/market.move:158:9+39
    $t14 := $UpdateMutation($t14, $Update'$0_market_ColData'_gross($Dereference($t14), $Dereference($t17)));

    // write_back[Reference($t0).contents (vector<vec_map::Entry<address, market::ColData>>)/[]/.value (market::ColData)]($t14) at ./sources/market.move:158:9+39
    $t0 := $UpdateMutation($t0, (var $$sel0 := $contents#$2_vec_map_VecMap'address_$0_market_ColData'($Dereference($t0)); $Update'$2_vec_map_VecMap'address_$0_market_ColData''_contents($Dereference($t0), (var $$sel1 := ReadVec($$sel0, ReadVec(p#$Mutation($t14), LenVec(p#$Mutation($t0)) + 1)); UpdateVec($$sel0, ReadVec(p#$Mutation($t14), LenVec(p#$Mutation($t0)) + 1), $Update'$2_vec_map_Entry'address_$0_market_ColData''_value($$sel1, $Dereference($t14)))))));

    // trace_local[collaterals]($t0) at ./sources/market.move:158:9+39
    $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' := $Dereference($t0);
    assume {:print "$track_local(15,0,0):", $temp_0'$2_vec_map_VecMap'address_$0_market_ColData''} $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' == $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'';

    // trace_local[collaterals]($t0) at ./sources/market.move:158:48+1
    $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' := $Dereference($t0);
    assume {:print "$track_local(15,0,0):", $temp_0'$2_vec_map_VecMap'address_$0_market_ColData''} $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' == $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'';

    // label L3 at ./sources/market.move:159:5+1
    assume {:print "$at(20,5989,5990)"} true;
L3:

    // return () at ./sources/market.move:159:5+1
    $ret0 := $t0;
    return;

    // label L4 at ./sources/market.move:159:5+1
L4:

    // abort($t9) at ./sources/market.move:159:5+1
    $abort_code := $t9;
    $abort_flag := true;
    return;

}

// fun market::add_col_value [verification] at ./sources/market.move:151:5+396
procedure {:timeLimit 40} $0_market_add_col_value$verify(_$t0: $Mutation ($2_vec_map_VecMap'address_$0_market_ColData'), _$t1: int, _$t2: int) returns ($ret0: $Mutation ($2_vec_map_VecMap'address_$0_market_ColData'))
{
    // declare local variables
    var $t3: $Mutation ($2_vec_map_VecMap'address_$0_market_ColData');
    var $t4: int;
    var $t5: $0_market_ColData;
    var $t6: $Mutation ($0_market_ColData);
    var $t7: $2_vec_map_VecMap'address_$0_market_ColData';
    var $t8: bool;
    var $t9: int;
    var $t10: bool;
    var $t11: int;
    var $t12: int;
    var $t13: $0_market_ColData;
    var $t14: $Mutation ($0_market_ColData);
    var $t15: int;
    var $t16: int;
    var $t17: $Mutation (int);
    var $t0: $Mutation ($2_vec_map_VecMap'address_$0_market_ColData');
    var $t1: int;
    var $t2: int;
    var $temp_0'$0_market_ColData': $0_market_ColData;
    var $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'': $2_vec_map_VecMap'address_$0_market_ColData';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;
    assume IsEmptyVec(p#$Mutation($t3));
    assume IsEmptyVec(p#$Mutation($t6));
    assume IsEmptyVec(p#$Mutation($t14));
    assume IsEmptyVec(p#$Mutation($t17));

    // verification entrypoint assumptions
    call $InitVerification();
    assume l#$Mutation($t0) == $Param(0);

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/market.move:151:5+1
    assume {:print "$at(20,5594,5595)"} true;
    assume $IsValid'$2_vec_map_VecMap'address_$0_market_ColData''($Dereference($t0));

    // assume WellFormed($t1) at ./sources/market.move:151:5+1
    assume $IsValid'address'($t1);

    // assume WellFormed($t2) at ./sources/market.move:151:5+1
    assume $IsValid'u64'($t2);

    // trace_local[collaterals]($t0) at ./sources/market.move:151:5+1
    $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' := $Dereference($t0);
    assume {:print "$track_local(15,0,0):", $temp_0'$2_vec_map_VecMap'address_$0_market_ColData''} $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' == $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'';

    // trace_local[sender]($t1) at ./sources/market.move:151:5+1
    assume {:print "$track_local(15,0,1):", $t1} $t1 == $t1;

    // trace_local[value]($t2) at ./sources/market.move:151:5+1
    assume {:print "$track_local(15,0,2):", $t2} $t2 == $t2;

    // $t7 := read_ref($t0) at ./sources/market.move:152:30+22
    assume {:print "$at(20,5716,5738)"} true;
    $t7 := $Dereference($t0);

    // $t8 := vec_map::contains<address, market::ColData>($t7, $t1) on_abort goto L4 with $t9 at ./sources/market.move:152:13+39
    call $t8 := $2_vec_map_contains'address_$0_market_ColData'($t7, $t1);
    if ($abort_flag) {
        assume {:print "$at(20,5699,5738)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(15,0):", $t9} $t9 == $t9;
        goto L4;
    }

    // $t10 := !($t8) at ./sources/market.move:152:12+1
    call $t10 := $Not($t8);

    // if ($t10) goto L0 else goto L2 at ./sources/market.move:152:9+175
    if ($t10) { goto L0; } else { goto L2; }

    // label L0 at ./sources/market.move:154:29+11
    assume {:print "$at(20,5829,5840)"} true;
L0:

    // $t11 := 0 at ./sources/market.move:153:43+1
    assume {:print "$at(20,5784,5785)"} true;
    $t11 := 0;
    assume $IsValid'u64'($t11);

    // $t12 := 0 at ./sources/market.move:153:56+1
    $t12 := 0;
    assume $IsValid'u64'($t12);

    // $t13 := pack market::ColData($t11, $t12) at ./sources/market.move:153:28+30
    $t13 := $0_market_ColData($t11, $t12);

    // vec_map::insert<address, market::ColData>($t0, $t1, $t13) on_abort goto L4 with $t9 at ./sources/market.move:154:13+46
    assume {:print "$at(20,5813,5859)"} true;
    call $t0 := $2_vec_map_insert'address_$0_market_ColData'($t0, $t1, $t13);
    if ($abort_flag) {
        assume {:print "$at(20,5813,5859)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(15,0):", $t9} $t9 == $t9;
        goto L4;
    }

    // label L2 at ./sources/market.move:157:41+11
    assume {:print "$at(20,5913,5924)"} true;
L2:

    // $t14 := vec_map::get_mut<address, market::ColData>($t0, $t1) on_abort goto L4 with $t9 at ./sources/market.move:157:24+38
    call $t14,$t0 := $2_vec_map_get_mut'address_$0_market_ColData'($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(20,5896,5934)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(15,0):", $t9} $t9 == $t9;
        goto L4;
    }

    // trace_local[col_data#3]($t14) at ./sources/market.move:157:13+8
    $temp_0'$0_market_ColData' := $Dereference($t14);
    assume {:print "$track_local(15,0,6):", $temp_0'$0_market_ColData'} $temp_0'$0_market_ColData' == $temp_0'$0_market_ColData';

    // $t15 := get_field<market::ColData>.gross($t14) at ./sources/market.move:158:26+14
    assume {:print "$at(20,5961,5975)"} true;
    $t15 := $gross#$0_market_ColData($Dereference($t14));

    // $t16 := +($t15, $t2) on_abort goto L4 with $t9 at ./sources/market.move:158:41+1
    call $t16 := $AddU64($t15, $t2);
    if ($abort_flag) {
        assume {:print "$at(20,5976,5977)"} true;
        $t9 := $abort_code;
        assume {:print "$track_abort(15,0):", $t9} $t9 == $t9;
        goto L4;
    }

    // $t17 := borrow_field<market::ColData>.gross($t14) at ./sources/market.move:158:9+14
    $t17 := $ChildMutation($t14, 0, $gross#$0_market_ColData($Dereference($t14)));

    // write_ref($t17, $t16) at ./sources/market.move:158:9+39
    $t17 := $UpdateMutation($t17, $t16);

    // write_back[Reference($t14).gross (u64)]($t17) at ./sources/market.move:158:9+39
    $t14 := $UpdateMutation($t14, $Update'$0_market_ColData'_gross($Dereference($t14), $Dereference($t17)));

    // write_back[Reference($t0).contents (vector<vec_map::Entry<address, market::ColData>>)/[]/.value (market::ColData)]($t14) at ./sources/market.move:158:9+39
    $t0 := $UpdateMutation($t0, (var $$sel0 := $contents#$2_vec_map_VecMap'address_$0_market_ColData'($Dereference($t0)); $Update'$2_vec_map_VecMap'address_$0_market_ColData''_contents($Dereference($t0), (var $$sel1 := ReadVec($$sel0, ReadVec(p#$Mutation($t14), LenVec(p#$Mutation($t0)) + 1)); UpdateVec($$sel0, ReadVec(p#$Mutation($t14), LenVec(p#$Mutation($t0)) + 1), $Update'$2_vec_map_Entry'address_$0_market_ColData''_value($$sel1, $Dereference($t14)))))));

    // trace_local[collaterals]($t0) at ./sources/market.move:158:9+39
    $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' := $Dereference($t0);
    assume {:print "$track_local(15,0,0):", $temp_0'$2_vec_map_VecMap'address_$0_market_ColData''} $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' == $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'';

    // trace_local[collaterals]($t0) at ./sources/market.move:158:48+1
    $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' := $Dereference($t0);
    assume {:print "$track_local(15,0,0):", $temp_0'$2_vec_map_VecMap'address_$0_market_ColData''} $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' == $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'';

    // label L3 at ./sources/market.move:159:5+1
    assume {:print "$at(20,5989,5990)"} true;
L3:

    // return () at ./sources/market.move:159:5+1
    $ret0 := $t0;
    return;

    // label L4 at ./sources/market.move:159:5+1
L4:

    // abort($t9) at ./sources/market.move:159:5+1
    $abort_code := $t9;
    $abort_flag := true;
    return;

}

// fun market::check_admin [baseline] at ./sources/market.move:138:5+250
procedure {:inline 1} $0_market_check_admin(_$t0: $0_market_Market, _$t1: $0_market_AdminCap) returns ()
{
    // declare local variables
    var $t2: $2_object_ID;
    var $t3: int;
    var $t4: $2_object_ID;
    var $t5: bool;
    var $t6: int;
    var $t0: $0_market_Market;
    var $t1: $0_market_AdminCap;
    var $temp_0'$0_market_AdminCap': $0_market_AdminCap;
    var $temp_0'$0_market_Market': $0_market_Market;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[market]($t0) at ./sources/market.move:138:5+1
    assume {:print "$at(20,5041,5042)"} true;
    assume {:print "$track_local(15,2,0):", $t0} $t0 == $t0;

    // trace_local[admin_cap]($t1) at ./sources/market.move:138:5+1
    assume {:print "$track_local(15,2,1):", $t1} $t1 == $t1;

    // $t2 := object::borrow_id<market::Market>($t0) on_abort goto L3 with $t3 at ./sources/market.move:140:17+25
    assume {:print "$at(20,5222,5247)"} true;
    call $t2 := $2_object_borrow_id'$0_market_Market'($t0);
    if ($abort_flag) {
        assume {:print "$at(20,5222,5247)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(15,2):", $t3} $t3 == $t3;
        goto L3;
    }

    // $t4 := get_field<market::AdminCap>.market_id($t1) at ./sources/market.move:140:46+20
    $t4 := $market_id#$0_market_AdminCap($t1);

    // $t5 := ==($t2, $t4) at ./sources/market.move:140:43+2
    $t5 := $IsEqual'$2_object_ID'($t2, $t4);

    // if ($t5) goto L0 else goto L1 at ./sources/market.move:140:9+70
    if ($t5) { goto L0; } else { goto L1; }

    // label L1 at ./sources/market.move:140:68+10
L1:

    // $t6 := 1 at ./sources/market.move:140:68+10
    $t6 := 1;
    assume $IsValid'u64'($t6);

    // trace_abort($t6) at ./sources/market.move:140:9+70
    assume {:print "$at(20,5214,5284)"} true;
    assume {:print "$track_abort(15,2):", $t6} $t6 == $t6;

    // $t3 := move($t6) at ./sources/market.move:140:9+70
    $t3 := $t6;

    // goto L3 at ./sources/market.move:140:9+70
    goto L3;

    // label L0 at ./sources/market.move:140:79+1
L0:

    // label L2 at ./sources/market.move:141:5+1
    assume {:print "$at(20,5290,5291)"} true;
L2:

    // return () at ./sources/market.move:141:5+1
    return;

    // label L3 at ./sources/market.move:141:5+1
L3:

    // abort($t3) at ./sources/market.move:141:5+1
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun market::check_admin [verification] at ./sources/market.move:138:5+250
procedure {:timeLimit 40} $0_market_check_admin$verify(_$t0: $0_market_Market, _$t1: $0_market_AdminCap) returns ()
{
    // declare local variables
    var $t2: $2_object_ID;
    var $t3: int;
    var $t4: $2_object_ID;
    var $t5: bool;
    var $t6: int;
    var $t0: $0_market_Market;
    var $t1: $0_market_AdminCap;
    var $temp_0'$0_market_AdminCap': $0_market_AdminCap;
    var $temp_0'$0_market_Market': $0_market_Market;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/market.move:138:5+1
    assume {:print "$at(20,5041,5042)"} true;
    assume $IsValid'$0_market_Market'($t0);

    // assume WellFormed($t1) at ./sources/market.move:138:5+1
    assume $IsValid'$0_market_AdminCap'($t1);

    // trace_local[market]($t0) at ./sources/market.move:138:5+1
    assume {:print "$track_local(15,2,0):", $t0} $t0 == $t0;

    // trace_local[admin_cap]($t1) at ./sources/market.move:138:5+1
    assume {:print "$track_local(15,2,1):", $t1} $t1 == $t1;

    // $t2 := object::borrow_id<market::Market>($t0) on_abort goto L3 with $t3 at ./sources/market.move:140:17+25
    assume {:print "$at(20,5222,5247)"} true;
    call $t2 := $2_object_borrow_id'$0_market_Market'($t0);
    if ($abort_flag) {
        assume {:print "$at(20,5222,5247)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(15,2):", $t3} $t3 == $t3;
        goto L3;
    }

    // $t4 := get_field<market::AdminCap>.market_id($t1) at ./sources/market.move:140:46+20
    $t4 := $market_id#$0_market_AdminCap($t1);

    // $t5 := ==($t2, $t4) at ./sources/market.move:140:43+2
    $t5 := $IsEqual'$2_object_ID'($t2, $t4);

    // if ($t5) goto L0 else goto L1 at ./sources/market.move:140:9+70
    if ($t5) { goto L0; } else { goto L1; }

    // label L1 at ./sources/market.move:140:68+10
L1:

    // $t6 := 1 at ./sources/market.move:140:68+10
    $t6 := 1;
    assume $IsValid'u64'($t6);

    // trace_abort($t6) at ./sources/market.move:140:9+70
    assume {:print "$at(20,5214,5284)"} true;
    assume {:print "$track_abort(15,2):", $t6} $t6 == $t6;

    // $t3 := move($t6) at ./sources/market.move:140:9+70
    $t3 := $t6;

    // goto L3 at ./sources/market.move:140:9+70
    goto L3;

    // label L0 at ./sources/market.move:140:79+1
L0:

    // label L2 at ./sources/market.move:141:5+1
    assume {:print "$at(20,5290,5291)"} true;
L2:

    // return () at ./sources/market.move:141:5+1
    return;

    // label L3 at ./sources/market.move:141:5+1
L3:

    // abort($t3) at ./sources/market.move:141:5+1
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun market::check_child<#0> [baseline] at ./sources/market.move:143:5+252
procedure {:inline 1} $0_market_check_child'#0'(_$t0: $0_market_Market, _$t1: $0_market_SubMarket'#0') returns ()
{
    // declare local variables
    var $t2: $2_object_ID;
    var $t3: $2_vec_set_VecSet'$2_object_ID';
    var $t4: $2_vec_set_VecSet'$2_object_ID';
    var $t5: $2_object_ID;
    var $t6: int;
    var $t7: bool;
    var $t8: bool;
    var $t9: bool;
    var $t10: int;
    var $t11: int;
    var $t0: $0_market_Market;
    var $t1: $0_market_SubMarket'#0';
    var $temp_0'$0_market_Market': $0_market_Market;
    var $temp_0'$0_market_SubMarket'#0'': $0_market_SubMarket'#0';
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[market]($t0) at ./sources/market.move:143:5+1
    assume {:print "$at(20,5297,5298)"} true;
    assume {:print "$track_local(15,3,0):", $t0} $t0 == $t0;

    // trace_local[sub_market]($t1) at ./sources/market.move:143:5+1
    assume {:print "$track_local(15,3,1):", $t1} $t1 == $t1;

    // $t4 := get_field<market::Market>.submarket_ids($t0) at ./sources/market.move:145:31+21
    assume {:print "$at(20,5416,5437)"} true;
    $t4 := $submarket_ids#$0_market_Market($t0);

    // $t5 := market::get_submarket_id<#0>($t1) on_abort goto L3 with $t6 at ./sources/market.move:145:55+28
    call $t5 := $0_market_get_submarket_id'#0'($t1);
    if ($abort_flag) {
        assume {:print "$at(20,5440,5468)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(15,3):", $t6} $t6 == $t6;
        goto L3;
    }

    // $t7 := vec_set::contains<object::ID>($t4, $t5) on_abort goto L3 with $t6 at ./sources/market.move:145:13+71
    call $t7 := $2_vec_set_contains'$2_object_ID'($t4, $t5);
    if ($abort_flag) {
        assume {:print "$at(20,5398,5469)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(15,3):", $t6} $t6 == $t6;
        goto L3;
    }

    // $t8 := true at ./sources/market.move:145:88+4
    $t8 := true;
    assume $IsValid'bool'($t8);

    // $t9 := ==($t7, $t8) at ./sources/market.move:145:85+2
    $t9 := $IsEqual'bool'($t7, $t8);

    // if ($t9) goto L0 else goto L1 at ./sources/market.move:144:9+166
    assume {:print "$at(20,5377,5543)"} true;
    if ($t9) { goto L0; } else { goto L1; }

    // label L1 at ./sources/market.move:146:38+16
    assume {:print "$at(20,5516,5532)"} true;
L1:

    // $t10 := 2 at ./sources/market.move:146:38+16
    $t10 := 2;
    assume $IsValid'u64'($t10);

    // $t11 := opaque begin: errors::invalid_argument($t10) at ./sources/market.move:146:13+42

    // assume WellFormed($t11) at ./sources/market.move:146:13+42
    assume $IsValid'u64'($t11);

    // assume Eq<u64>($t11, 7) at ./sources/market.move:146:13+42
    assume $IsEqual'u64'($t11, 7);

    // $t11 := opaque end: errors::invalid_argument($t10) at ./sources/market.move:146:13+42

    // trace_abort($t11) at ./sources/market.move:144:9+166
    assume {:print "$at(20,5377,5543)"} true;
    assume {:print "$track_abort(15,3):", $t11} $t11 == $t11;

    // $t6 := move($t11) at ./sources/market.move:144:9+166
    $t6 := $t11;

    // goto L3 at ./sources/market.move:144:9+166
    goto L3;

    // label L0 at ./sources/market.move:144:9+166
L0:

    // label L2 at ./sources/market.move:148:5+1
    assume {:print "$at(20,5548,5549)"} true;
L2:

    // return () at ./sources/market.move:148:5+1
    return;

    // label L3 at ./sources/market.move:148:5+1
L3:

    // abort($t6) at ./sources/market.move:148:5+1
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun market::check_child<#1> [baseline] at ./sources/market.move:143:5+252
procedure {:inline 1} $0_market_check_child'#1'(_$t0: $0_market_Market, _$t1: $0_market_SubMarket'#1') returns ()
{
    // declare local variables
    var $t2: $2_object_ID;
    var $t3: $2_vec_set_VecSet'$2_object_ID';
    var $t4: $2_vec_set_VecSet'$2_object_ID';
    var $t5: $2_object_ID;
    var $t6: int;
    var $t7: bool;
    var $t8: bool;
    var $t9: bool;
    var $t10: int;
    var $t11: int;
    var $t0: $0_market_Market;
    var $t1: $0_market_SubMarket'#1';
    var $temp_0'$0_market_Market': $0_market_Market;
    var $temp_0'$0_market_SubMarket'#1'': $0_market_SubMarket'#1';
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[market]($t0) at ./sources/market.move:143:5+1
    assume {:print "$at(20,5297,5298)"} true;
    assume {:print "$track_local(15,3,0):", $t0} $t0 == $t0;

    // trace_local[sub_market]($t1) at ./sources/market.move:143:5+1
    assume {:print "$track_local(15,3,1):", $t1} $t1 == $t1;

    // $t4 := get_field<market::Market>.submarket_ids($t0) at ./sources/market.move:145:31+21
    assume {:print "$at(20,5416,5437)"} true;
    $t4 := $submarket_ids#$0_market_Market($t0);

    // $t5 := market::get_submarket_id<#0>($t1) on_abort goto L3 with $t6 at ./sources/market.move:145:55+28
    call $t5 := $0_market_get_submarket_id'#1'($t1);
    if ($abort_flag) {
        assume {:print "$at(20,5440,5468)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(15,3):", $t6} $t6 == $t6;
        goto L3;
    }

    // $t7 := vec_set::contains<object::ID>($t4, $t5) on_abort goto L3 with $t6 at ./sources/market.move:145:13+71
    call $t7 := $2_vec_set_contains'$2_object_ID'($t4, $t5);
    if ($abort_flag) {
        assume {:print "$at(20,5398,5469)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(15,3):", $t6} $t6 == $t6;
        goto L3;
    }

    // $t8 := true at ./sources/market.move:145:88+4
    $t8 := true;
    assume $IsValid'bool'($t8);

    // $t9 := ==($t7, $t8) at ./sources/market.move:145:85+2
    $t9 := $IsEqual'bool'($t7, $t8);

    // if ($t9) goto L0 else goto L1 at ./sources/market.move:144:9+166
    assume {:print "$at(20,5377,5543)"} true;
    if ($t9) { goto L0; } else { goto L1; }

    // label L1 at ./sources/market.move:146:38+16
    assume {:print "$at(20,5516,5532)"} true;
L1:

    // $t10 := 2 at ./sources/market.move:146:38+16
    $t10 := 2;
    assume $IsValid'u64'($t10);

    // $t11 := opaque begin: errors::invalid_argument($t10) at ./sources/market.move:146:13+42

    // assume WellFormed($t11) at ./sources/market.move:146:13+42
    assume $IsValid'u64'($t11);

    // assume Eq<u64>($t11, 7) at ./sources/market.move:146:13+42
    assume $IsEqual'u64'($t11, 7);

    // $t11 := opaque end: errors::invalid_argument($t10) at ./sources/market.move:146:13+42

    // trace_abort($t11) at ./sources/market.move:144:9+166
    assume {:print "$at(20,5377,5543)"} true;
    assume {:print "$track_abort(15,3):", $t11} $t11 == $t11;

    // $t6 := move($t11) at ./sources/market.move:144:9+166
    $t6 := $t11;

    // goto L3 at ./sources/market.move:144:9+166
    goto L3;

    // label L0 at ./sources/market.move:144:9+166
L0:

    // label L2 at ./sources/market.move:148:5+1
    assume {:print "$at(20,5548,5549)"} true;
L2:

    // return () at ./sources/market.move:148:5+1
    return;

    // label L3 at ./sources/market.move:148:5+1
L3:

    // abort($t6) at ./sources/market.move:148:5+1
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun market::check_child [verification] at ./sources/market.move:143:5+252
procedure {:timeLimit 40} $0_market_check_child$verify(_$t0: $0_market_Market, _$t1: $0_market_SubMarket'#0') returns ()
{
    // declare local variables
    var $t2: $2_object_ID;
    var $t3: $2_vec_set_VecSet'$2_object_ID';
    var $t4: $2_vec_set_VecSet'$2_object_ID';
    var $t5: $2_object_ID;
    var $t6: int;
    var $t7: bool;
    var $t8: bool;
    var $t9: bool;
    var $t10: int;
    var $t11: int;
    var $t0: $0_market_Market;
    var $t1: $0_market_SubMarket'#0';
    var $temp_0'$0_market_Market': $0_market_Market;
    var $temp_0'$0_market_SubMarket'#0'': $0_market_SubMarket'#0';
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/market.move:143:5+1
    assume {:print "$at(20,5297,5298)"} true;
    assume $IsValid'$0_market_Market'($t0);

    // assume WellFormed($t1) at ./sources/market.move:143:5+1
    assume $IsValid'$0_market_SubMarket'#0''($t1);

    // trace_local[market]($t0) at ./sources/market.move:143:5+1
    assume {:print "$track_local(15,3,0):", $t0} $t0 == $t0;

    // trace_local[sub_market]($t1) at ./sources/market.move:143:5+1
    assume {:print "$track_local(15,3,1):", $t1} $t1 == $t1;

    // $t4 := get_field<market::Market>.submarket_ids($t0) at ./sources/market.move:145:31+21
    assume {:print "$at(20,5416,5437)"} true;
    $t4 := $submarket_ids#$0_market_Market($t0);

    // $t5 := market::get_submarket_id<#0>($t1) on_abort goto L3 with $t6 at ./sources/market.move:145:55+28
    call $t5 := $0_market_get_submarket_id'#0'($t1);
    if ($abort_flag) {
        assume {:print "$at(20,5440,5468)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(15,3):", $t6} $t6 == $t6;
        goto L3;
    }

    // $t7 := vec_set::contains<object::ID>($t4, $t5) on_abort goto L3 with $t6 at ./sources/market.move:145:13+71
    call $t7 := $2_vec_set_contains'$2_object_ID'($t4, $t5);
    if ($abort_flag) {
        assume {:print "$at(20,5398,5469)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(15,3):", $t6} $t6 == $t6;
        goto L3;
    }

    // $t8 := true at ./sources/market.move:145:88+4
    $t8 := true;
    assume $IsValid'bool'($t8);

    // $t9 := ==($t7, $t8) at ./sources/market.move:145:85+2
    $t9 := $IsEqual'bool'($t7, $t8);

    // if ($t9) goto L0 else goto L1 at ./sources/market.move:144:9+166
    assume {:print "$at(20,5377,5543)"} true;
    if ($t9) { goto L0; } else { goto L1; }

    // label L1 at ./sources/market.move:146:38+16
    assume {:print "$at(20,5516,5532)"} true;
L1:

    // $t10 := 2 at ./sources/market.move:146:38+16
    $t10 := 2;
    assume $IsValid'u64'($t10);

    // $t11 := opaque begin: errors::invalid_argument($t10) at ./sources/market.move:146:13+42

    // assume WellFormed($t11) at ./sources/market.move:146:13+42
    assume $IsValid'u64'($t11);

    // assume Eq<u64>($t11, 7) at ./sources/market.move:146:13+42
    assume $IsEqual'u64'($t11, 7);

    // $t11 := opaque end: errors::invalid_argument($t10) at ./sources/market.move:146:13+42

    // trace_abort($t11) at ./sources/market.move:144:9+166
    assume {:print "$at(20,5377,5543)"} true;
    assume {:print "$track_abort(15,3):", $t11} $t11 == $t11;

    // $t6 := move($t11) at ./sources/market.move:144:9+166
    $t6 := $t11;

    // goto L3 at ./sources/market.move:144:9+166
    goto L3;

    // label L0 at ./sources/market.move:144:9+166
L0:

    // label L2 at ./sources/market.move:148:5+1
    assume {:print "$at(20,5548,5549)"} true;
L2:

    // return () at ./sources/market.move:148:5+1
    return;

    // label L3 at ./sources/market.move:148:5+1
L3:

    // abort($t6) at ./sources/market.move:148:5+1
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun market::create_market [verification] at ./sources/market.move:56:5+556
procedure {:timeLimit 40} $0_market_create_market$verify(_$t0: $Mutation ($2_tx_context_TxContext)) returns ($ret0: $Mutation ($2_tx_context_TxContext))
{
    // declare local variables
    var $t1: $0_market_AdminCap;
    var $t2: $0_market_Market;
    var $t3: $2_object_UID;
    var $t4: int;
    var $t5: $2_vec_set_VecSet'$2_object_ID';
    var $t6: Vec ($2_object_ID);
    var $t7: $0_market_Market;
    var $t8: $2_object_UID;
    var $t9: $2_object_ID;
    var $t10: $0_market_AdminCap;
    var $t11: $2_tx_context_TxContext;
    var $t12: int;
    var $t0: $Mutation ($2_tx_context_TxContext);
    var $temp_0'$0_market_AdminCap': $0_market_AdminCap;
    var $temp_0'$0_market_Market': $0_market_Market;
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();
    assume l#$Mutation($t0) == $Param(0);

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/market.move:56:5+1
    assume {:print "$at(20,1412,1413)"} true;
    assume $IsValid'$2_tx_context_TxContext'($Dereference($t0));

    // trace_local[ctx]($t0) at ./sources/market.move:56:5+1
    $temp_0'$2_tx_context_TxContext' := $Dereference($t0);
    assume {:print "$track_local(15,4,0):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // $t3 := object::new($t0) on_abort goto L2 with $t4 at ./sources/market.move:58:17+16
    assume {:print "$at(20,1511,1527)"} true;
    call $t3,$t0 := $2_object_new($t0);
    if ($abort_flag) {
        assume {:print "$at(20,1511,1527)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(15,4):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t5 := vec_set::empty<object::ID>() on_abort goto L2 with $t4 at ./sources/market.move:59:28+16
    assume {:print "$at(20,1556,1572)"} true;
    call $t5 := $2_vec_set_empty'$2_object_ID'();
    if ($abort_flag) {
        assume {:print "$at(20,1556,1572)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(15,4):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t6 := vector::empty<object::ID>() on_abort goto L2 with $t4 at ./sources/market.move:60:32+15
    assume {:print "$at(20,1605,1620)"} true;
    call $t6 := $1_vector_empty'$2_object_ID'();
    if ($abort_flag) {
        assume {:print "$at(20,1605,1620)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(15,4):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t7 := pack market::Market($t3, $t5, $t6) at ./sources/market.move:57:22+143
    assume {:print "$at(20,1487,1630)"} true;
    $t7 := $0_market_Market($t3, $t5, $t6);

    // trace_local[market]($t7) at ./sources/market.move:57:13+6
    assume {:print "$track_local(15,4,2):", $t7} $t7 == $t7;

    // $t8 := object::new($t0) on_abort goto L2 with $t4 at ./sources/market.move:62:38+16
    assume {:print "$at(20,1669,1685)"} true;
    call $t8,$t0 := $2_object_new($t0);
    if ($abort_flag) {
        assume {:print "$at(20,1669,1685)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(15,4):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t9 := market::get_market_id($t7) on_abort goto L2 with $t4 at ./sources/market.move:62:67+22
    call $t9 := $0_market_get_market_id($t7);
    if ($abort_flag) {
        assume {:print "$at(20,1698,1720)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(15,4):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t10 := pack market::AdminCap($t8, $t9) at ./sources/market.move:62:25+65
    $t10 := $0_market_AdminCap($t8, $t9);

    // trace_local[admin_cap]($t10) at ./sources/market.move:62:13+9
    assume {:print "$track_local(15,4,1):", $t10} $t10 == $t10;

    // transfer::share_object<market::Market>($t7) on_abort goto L2 with $t4 at ./sources/market.move:65:9+30
    assume {:print "$at(20,1812,1842)"} true;
    call $2_transfer_share_object'$0_market_Market'($t7);
    if ($abort_flag) {
        assume {:print "$at(20,1812,1842)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(15,4):", $t4} $t4 == $t4;
        goto L2;
    }

    // $t11 := read_ref($t0) at ./sources/market.move:67:58+3
    assume {:print "$at(20,1956,1959)"} true;
    $t11 := $Dereference($t0);

    // $t12 := tx_context::sender($t11) on_abort goto L2 with $t4 at ./sources/market.move:67:39+23
    call $t12 := $2_tx_context_sender($t11);
    if ($abort_flag) {
        assume {:print "$at(20,1937,1960)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(15,4):", $t4} $t4 == $t4;
        goto L2;
    }

    // transfer::transfer<market::AdminCap>($t10, $t12) on_abort goto L2 with $t4 at ./sources/market.move:67:9+54
    call $2_transfer_transfer'$0_market_AdminCap'($t10, $t12);
    if ($abort_flag) {
        assume {:print "$at(20,1907,1961)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(15,4):", $t4} $t4 == $t4;
        goto L2;
    }

    // trace_local[ctx]($t0) at ./sources/market.move:67:63+1
    $temp_0'$2_tx_context_TxContext' := $Dereference($t0);
    assume {:print "$track_local(15,4,0):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // label L1 at ./sources/market.move:68:5+1
    assume {:print "$at(20,1967,1968)"} true;
L1:

    // return () at ./sources/market.move:68:5+1
    $ret0 := $t0;
    return;

    // label L2 at ./sources/market.move:68:5+1
L2:

    // abort($t4) at ./sources/market.move:68:5+1
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun market::create_sub_market [verification] at ./sources/market.move:70:5+659
procedure {:timeLimit 40} $0_market_create_sub_market$verify(_$t0: $Mutation ($0_market_Market), _$t1: $Mutation ($0_market_AdminCap), _$t2: $Mutation ($2_tx_context_TxContext)) returns ($ret0: $Mutation ($0_market_Market), $ret1: $Mutation ($0_market_AdminCap), $ret2: $Mutation ($2_tx_context_TxContext))
{
    // declare local variables
    var $t3: $Mutation ($0_market_Market);
    var $t4: $Mutation ($0_market_AdminCap);
    var $t5: $0_market_SubMarket'#0';
    var $t6: $2_object_UID;
    var $t7: int;
    var $t8: $2_balance_Balance'#0';
    var $t9: $2_vec_map_VecMap'address_$0_market_ColData';
    var $t10: $0_market_SubMarket'#0';
    var $t11: $0_market_Market;
    var $t12: $0_market_AdminCap;
    var $t13: $Mutation ($2_vec_set_VecSet'$2_object_ID');
    var $t14: $2_object_ID;
    var $t0: $Mutation ($0_market_Market);
    var $t1: $Mutation ($0_market_AdminCap);
    var $t2: $Mutation ($2_tx_context_TxContext);
    var $temp_0'$0_market_AdminCap': $0_market_AdminCap;
    var $temp_0'$0_market_Market': $0_market_Market;
    var $temp_0'$0_market_SubMarket'#0'': $0_market_SubMarket'#0';
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;
    assume IsEmptyVec(p#$Mutation($t3));
    assume IsEmptyVec(p#$Mutation($t4));
    assume IsEmptyVec(p#$Mutation($t13));

    // verification entrypoint assumptions
    call $InitVerification();
    assume l#$Mutation($t0) == $Param(0);
    assume l#$Mutation($t1) == $Param(1);
    assume l#$Mutation($t2) == $Param(2);

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/market.move:70:5+1
    assume {:print "$at(20,1974,1975)"} true;
    assume $IsValid'$0_market_Market'($Dereference($t0));

    // assume WellFormed($t1) at ./sources/market.move:70:5+1
    assume $IsValid'$0_market_AdminCap'($Dereference($t1));

    // assume WellFormed($t2) at ./sources/market.move:70:5+1
    assume $IsValid'$2_tx_context_TxContext'($Dereference($t2));

    // trace_local[market]($t0) at ./sources/market.move:70:5+1
    $temp_0'$0_market_Market' := $Dereference($t0);
    assume {:print "$track_local(15,5,0):", $temp_0'$0_market_Market'} $temp_0'$0_market_Market' == $temp_0'$0_market_Market';

    // trace_local[admin_cap]($t1) at ./sources/market.move:70:5+1
    $temp_0'$0_market_AdminCap' := $Dereference($t1);
    assume {:print "$track_local(15,5,1):", $temp_0'$0_market_AdminCap'} $temp_0'$0_market_AdminCap' == $temp_0'$0_market_AdminCap';

    // trace_local[ctx]($t2) at ./sources/market.move:70:5+1
    $temp_0'$2_tx_context_TxContext' := $Dereference($t2);
    assume {:print "$track_local(15,5,2):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // $t6 := object::new($t2) on_abort goto L2 with $t7 at ./sources/market.move:72:17+16
    assume {:print "$at(20,2137,2153)"} true;
    call $t6,$t2 := $2_object_new($t2);
    if ($abort_flag) {
        assume {:print "$at(20,2137,2153)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(15,5):", $t7} $t7 == $t7;
        goto L2;
    }

    // $t8 := balance::zero<#0>() on_abort goto L2 with $t7 at ./sources/market.move:73:22+15
    assume {:print "$at(20,2176,2191)"} true;
    call $t8 := $2_balance_zero'#0'();
    if ($abort_flag) {
        assume {:print "$at(20,2176,2191)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(15,5):", $t7} $t7 == $t7;
        goto L2;
    }

    // $t9 := vec_map::empty<address, market::ColData>() on_abort goto L2 with $t7 at ./sources/market.move:74:26+16
    assume {:print "$at(20,2218,2234)"} true;
    call $t9 := $2_vec_map_empty'address_$0_market_ColData'();
    if ($abort_flag) {
        assume {:print "$at(20,2218,2234)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(15,5):", $t7} $t7 == $t7;
        goto L2;
    }

    // $t10 := pack market::SubMarket<#0>($t6, $t8, $t9) at ./sources/market.move:71:26+137
    assume {:print "$at(20,2107,2244)"} true;
    $t10 := $0_market_SubMarket'#0'($t6, $t8, $t9);

    // trace_local[sub_market]($t10) at ./sources/market.move:71:13+10
    assume {:print "$track_local(15,5,5):", $t10} $t10 == $t10;

    // $t11 := read_ref($t0) at ./sources/market.move:78:20+19
    assume {:print "$at(20,2350,2369)"} true;
    $t11 := $Dereference($t0);

    // $t12 := read_ref($t1) at ./sources/market.move:78:20+19
    $t12 := $Dereference($t1);

    // market::check_admin($t11, $t12) on_abort goto L2 with $t7 at ./sources/market.move:78:9+30
    call $0_market_check_admin($t11, $t12);
    if ($abort_flag) {
        assume {:print "$at(20,2339,2369)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(15,5):", $t7} $t7 == $t7;
        goto L2;
    }

    // $t13 := borrow_field<market::Market>.submarket_ids($t0) at ./sources/market.move:80:25+25
    assume {:print "$at(20,2453,2478)"} true;
    $t13 := $ChildMutation($t0, 1, $submarket_ids#$0_market_Market($Dereference($t0)));

    // $t14 := market::get_submarket_id<#0>($t10) on_abort goto L2 with $t7 at ./sources/market.move:80:52+32
    call $t14 := $0_market_get_submarket_id'#0'($t10);
    if ($abort_flag) {
        assume {:print "$at(20,2480,2512)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(15,5):", $t7} $t7 == $t7;
        goto L2;
    }

    // vec_set::insert<object::ID>($t13, $t14) on_abort goto L2 with $t7 at ./sources/market.move:80:9+76
    call $t13 := $2_vec_set_insert'$2_object_ID'($t13, $t14);
    if ($abort_flag) {
        assume {:print "$at(20,2437,2513)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(15,5):", $t7} $t7 == $t7;
        goto L2;
    }

    // write_back[Reference($t0).submarket_ids (vec_set::VecSet<object::ID>)]($t13) at ./sources/market.move:80:9+76
    $t0 := $UpdateMutation($t0, $Update'$0_market_Market'_submarket_ids($Dereference($t0), $Dereference($t13)));

    // trace_local[market]($t0) at ./sources/market.move:80:9+76
    $temp_0'$0_market_Market' := $Dereference($t0);
    assume {:print "$track_local(15,5,0):", $temp_0'$0_market_Market'} $temp_0'$0_market_Market' == $temp_0'$0_market_Market';

    // transfer::transfer_to_object<market::SubMarket<#0>, market::Market>($t10, $t0) on_abort goto L2 with $t7 at ./sources/market.move:82:9+48
    assume {:print "$at(20,2578,2626)"} true;
    call $t0 := $2_transfer_transfer_to_object'$0_market_SubMarket'#0'_$0_market_Market'($t10, $t0);
    if ($abort_flag) {
        assume {:print "$at(20,2578,2626)"} true;
        $t7 := $abort_code;
        assume {:print "$track_abort(15,5):", $t7} $t7 == $t7;
        goto L2;
    }

    // trace_local[market]($t0) at ./sources/market.move:82:57+1
    $temp_0'$0_market_Market' := $Dereference($t0);
    assume {:print "$track_local(15,5,0):", $temp_0'$0_market_Market'} $temp_0'$0_market_Market' == $temp_0'$0_market_Market';

    // trace_local[admin_cap]($t1) at ./sources/market.move:82:57+1
    $temp_0'$0_market_AdminCap' := $Dereference($t1);
    assume {:print "$track_local(15,5,1):", $temp_0'$0_market_AdminCap'} $temp_0'$0_market_AdminCap' == $temp_0'$0_market_AdminCap';

    // trace_local[ctx]($t2) at ./sources/market.move:82:57+1
    $temp_0'$2_tx_context_TxContext' := $Dereference($t2);
    assume {:print "$track_local(15,5,2):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // label L1 at ./sources/market.move:83:5+1
    assume {:print "$at(20,2632,2633)"} true;
L1:

    // return () at ./sources/market.move:83:5+1
    $ret0 := $t0;
    $ret1 := $t1;
    $ret2 := $t2;
    return;

    // label L2 at ./sources/market.move:83:5+1
L2:

    // abort($t7) at ./sources/market.move:83:5+1
    $abort_code := $t7;
    $abort_flag := true;
    return;

}

// fun market::deposit_collateral [verification] at ./sources/market.move:85:5+631
procedure {:timeLimit 40} $0_market_deposit_collateral$verify(_$t0: $Mutation ($0_market_Market), _$t1: $Mutation ($0_market_SubMarket'#0'), _$t2: $2_coin_Coin'#0', _$t3: $Mutation ($2_tx_context_TxContext)) returns ($ret0: $Mutation ($0_market_Market), $ret1: $Mutation ($0_market_SubMarket'#0'), $ret2: $Mutation ($2_tx_context_TxContext))
{
    // declare local variables
    var $t4: $Mutation ($0_market_Market);
    var $t5: $Mutation ($0_market_SubMarket'#0');
    var $t6: $2_balance_Balance'#0';
    var $t7: int;
    var $t8: $0_market_Market;
    var $t9: $0_market_SubMarket'#0';
    var $t10: int;
    var $t11: $2_balance_Balance'#0';
    var $t12: int;
    var $t13: int;
    var $t14: bool;
    var $t15: int;
    var $t16: int;
    var $t17: $Mutation ($2_balance_Balance'#0');
    var $t18: int;
    var $t19: $Mutation ($2_vec_map_VecMap'address_$0_market_ColData');
    var $t20: $2_tx_context_TxContext;
    var $t21: int;
    var $t0: $Mutation ($0_market_Market);
    var $t1: $Mutation ($0_market_SubMarket'#0');
    var $t2: $2_coin_Coin'#0';
    var $t3: $Mutation ($2_tx_context_TxContext);
    var $temp_0'$0_market_Market': $0_market_Market;
    var $temp_0'$0_market_SubMarket'#0'': $0_market_SubMarket'#0';
    var $temp_0'$2_balance_Balance'#0'': $2_balance_Balance'#0';
    var $temp_0'$2_coin_Coin'#0'': $2_coin_Coin'#0';
    var $temp_0'$2_tx_context_TxContext': $2_tx_context_TxContext;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;
    $t3 := _$t3;
    assume IsEmptyVec(p#$Mutation($t4));
    assume IsEmptyVec(p#$Mutation($t5));
    assume IsEmptyVec(p#$Mutation($t17));
    assume IsEmptyVec(p#$Mutation($t19));

    // verification entrypoint assumptions
    call $InitVerification();
    assume l#$Mutation($t0) == $Param(0);
    assume l#$Mutation($t1) == $Param(1);
    assume l#$Mutation($t3) == $Param(3);

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/market.move:85:5+1
    assume {:print "$at(20,2639,2640)"} true;
    assume $IsValid'$0_market_Market'($Dereference($t0));

    // assume WellFormed($t1) at ./sources/market.move:85:5+1
    assume $IsValid'$0_market_SubMarket'#0''($Dereference($t1));

    // assume WellFormed($t2) at ./sources/market.move:85:5+1
    assume $IsValid'$2_coin_Coin'#0''($t2);

    // assume WellFormed($t3) at ./sources/market.move:85:5+1
    assume $IsValid'$2_tx_context_TxContext'($Dereference($t3));

    // trace_local[market]($t0) at ./sources/market.move:85:5+1
    $temp_0'$0_market_Market' := $Dereference($t0);
    assume {:print "$track_local(15,6,0):", $temp_0'$0_market_Market'} $temp_0'$0_market_Market' == $temp_0'$0_market_Market';

    // trace_local[sub_market]($t1) at ./sources/market.move:85:5+1
    $temp_0'$0_market_SubMarket'#0'' := $Dereference($t1);
    assume {:print "$track_local(15,6,1):", $temp_0'$0_market_SubMarket'#0''} $temp_0'$0_market_SubMarket'#0'' == $temp_0'$0_market_SubMarket'#0'';

    // trace_local[collateral]($t2) at ./sources/market.move:85:5+1
    assume {:print "$track_local(15,6,2):", $t2} $t2 == $t2;

    // trace_local[ctx]($t3) at ./sources/market.move:85:5+1
    $temp_0'$2_tx_context_TxContext' := $Dereference($t3);
    assume {:print "$track_local(15,6,3):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // $t8 := read_ref($t0) at ./sources/market.move:89:20+20
    assume {:print "$at(20,2857,2877)"} true;
    $t8 := $Dereference($t0);

    // $t9 := read_ref($t1) at ./sources/market.move:89:20+20
    $t9 := $Dereference($t1);

    // market::check_child<#0>($t8, $t9) on_abort goto L4 with $t10 at ./sources/market.move:89:9+31
    call $0_market_check_child'#0'($t8, $t9);
    if ($abort_flag) {
        assume {:print "$at(20,2846,2877)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(15,6):", $t10} $t10 == $t10;
        goto L4;
    }

    // $t11 := coin::into_balance<#0>($t2) on_abort goto L4 with $t10 at ./sources/market.move:91:34+30
    assume {:print "$at(20,2913,2943)"} true;
    call $t11 := $2_coin_into_balance'#0'($t2);
    if ($abort_flag) {
        assume {:print "$at(20,2913,2943)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(15,6):", $t10} $t10 == $t10;
        goto L4;
    }

    // trace_local[collateral_balance]($t11) at ./sources/market.move:91:13+18
    assume {:print "$track_local(15,6,6):", $t11} $t11 == $t11;

    // $t12 := balance::value<#0>($t11) on_abort goto L4 with $t10 at ./sources/market.move:92:32+35
    assume {:print "$at(20,2976,3011)"} true;
    call $t12 := $2_balance_value'#0'($t11);
    if ($abort_flag) {
        assume {:print "$at(20,2976,3011)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(15,6):", $t10} $t10 == $t10;
        goto L4;
    }

    // trace_local[collateral_value]($t12) at ./sources/market.move:92:13+16
    assume {:print "$track_local(15,6,7):", $t12} $t12 == $t12;

    // $t13 := 0 at ./sources/market.move:94:36+1
    assume {:print "$at(20,3049,3050)"} true;
    $t13 := 0;
    assume $IsValid'u64'($t13);

    // $t14 := >($t12, $t13) at ./sources/market.move:94:34+1
    call $t14 := $Gt($t12, $t13);

    // if ($t14) goto L0 else goto L2 at ./sources/market.move:94:9+77
    if ($t14) { goto L0; } else { goto L2; }

    // label L1 at ./sources/market.move:94:9+77
L1:

    // destroy($t1) at ./sources/market.move:94:9+77

    // destroy($t3) at ./sources/market.move:94:9+77

    // $t15 := 3 at ./sources/market.move:94:64+20
    $t15 := 3;
    assume $IsValid'u64'($t15);

    // $t16 := opaque begin: errors::invalid_argument($t15) at ./sources/market.move:94:39+46

    // assume WellFormed($t16) at ./sources/market.move:94:39+46
    assume $IsValid'u64'($t16);

    // assume Eq<u64>($t16, 7) at ./sources/market.move:94:39+46
    assume $IsEqual'u64'($t16, 7);

    // $t16 := opaque end: errors::invalid_argument($t15) at ./sources/market.move:94:39+46

    // trace_abort($t16) at ./sources/market.move:94:9+77
    assume {:print "$at(20,3022,3099)"} true;
    assume {:print "$track_abort(15,6):", $t16} $t16 == $t16;

    // $t10 := move($t16) at ./sources/market.move:94:9+77
    $t10 := $t16;

    // goto L4 at ./sources/market.move:94:9+77
    goto L4;

    // label L0 at ./sources/market.move:96:28+10
    assume {:print "$at(20,3129,3139)"} true;
L0:

    // $t17 := borrow_field<market::SubMarket<#0>>.balance($t1) at ./sources/market.move:96:23+23
    $t17 := $ChildMutation($t1, 1, $balance#$0_market_SubMarket'#0'($Dereference($t1)));

    // $t18 := balance::join<#0>($t17, $t11) on_abort goto L4 with $t10 at ./sources/market.move:96:9+58
    call $t18,$t17 := $2_balance_join'#0'($t17, $t11);
    if ($abort_flag) {
        assume {:print "$at(20,3110,3168)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(15,6):", $t10} $t10 == $t10;
        goto L4;
    }

    // write_back[Reference($t1).balance (balance::Balance<#0>)]($t17) at ./sources/market.move:96:9+58
    $t1 := $UpdateMutation($t1, $Update'$0_market_SubMarket'#0''_balance($Dereference($t1), $Dereference($t17)));

    // trace_local[sub_market]($t1) at ./sources/market.move:96:9+58
    $temp_0'$0_market_SubMarket'#0'' := $Dereference($t1);
    assume {:print "$track_local(15,6,1):", $temp_0'$0_market_SubMarket'#0''} $temp_0'$0_market_SubMarket'#0'' == $temp_0'$0_market_SubMarket'#0'';

    // destroy($t18) at ./sources/market.move:96:9+58

    // $t19 := borrow_field<market::SubMarket<#0>>.collaterals($t1) at ./sources/market.move:97:23+27
    assume {:print "$at(20,3192,3219)"} true;
    $t19 := $ChildMutation($t1, 2, $collaterals#$0_market_SubMarket'#0'($Dereference($t1)));

    // $t20 := read_ref($t3) at ./sources/market.move:97:71+3
    $t20 := $Dereference($t3);

    // $t21 := tx_context::sender($t20) on_abort goto L4 with $t10 at ./sources/market.move:97:52+23
    call $t21 := $2_tx_context_sender($t20);
    if ($abort_flag) {
        assume {:print "$at(20,3221,3244)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(15,6):", $t10} $t10 == $t10;
        goto L4;
    }

    // market::add_col_value($t19, $t21, $t12) on_abort goto L4 with $t10 at ./sources/market.move:97:9+85
    call $t19 := $0_market_add_col_value($t19, $t21, $t12);
    if ($abort_flag) {
        assume {:print "$at(20,3178,3263)"} true;
        $t10 := $abort_code;
        assume {:print "$track_abort(15,6):", $t10} $t10 == $t10;
        goto L4;
    }

    // write_back[Reference($t1).collaterals (vec_map::VecMap<address, market::ColData>)]($t19) at ./sources/market.move:97:9+85
    $t1 := $UpdateMutation($t1, $Update'$0_market_SubMarket'#0''_collaterals($Dereference($t1), $Dereference($t19)));

    // trace_local[sub_market]($t1) at ./sources/market.move:97:9+85
    $temp_0'$0_market_SubMarket'#0'' := $Dereference($t1);
    assume {:print "$track_local(15,6,1):", $temp_0'$0_market_SubMarket'#0''} $temp_0'$0_market_SubMarket'#0'' == $temp_0'$0_market_SubMarket'#0'';

    // trace_local[market]($t0) at ./sources/market.move:97:94+1
    $temp_0'$0_market_Market' := $Dereference($t0);
    assume {:print "$track_local(15,6,0):", $temp_0'$0_market_Market'} $temp_0'$0_market_Market' == $temp_0'$0_market_Market';

    // trace_local[sub_market]($t1) at ./sources/market.move:97:94+1
    $temp_0'$0_market_SubMarket'#0'' := $Dereference($t1);
    assume {:print "$track_local(15,6,1):", $temp_0'$0_market_SubMarket'#0''} $temp_0'$0_market_SubMarket'#0'' == $temp_0'$0_market_SubMarket'#0'';

    // trace_local[ctx]($t3) at ./sources/market.move:97:94+1
    $temp_0'$2_tx_context_TxContext' := $Dereference($t3);
    assume {:print "$track_local(15,6,3):", $temp_0'$2_tx_context_TxContext'} $temp_0'$2_tx_context_TxContext' == $temp_0'$2_tx_context_TxContext';

    // goto L3 at ./sources/market.move:97:94+1
    goto L3;

    // label L2 at <internal>:1:1+10
    assume {:print "$at(1,0,10)"} true;
L2:

    // destroy($t0) at <internal>:1:1+10

    // goto L1 at <internal>:1:1+10
    goto L1;

    // label L3 at ./sources/market.move:98:5+1
    assume {:print "$at(20,3269,3270)"} true;
L3:

    // return () at ./sources/market.move:98:5+1
    $ret0 := $t0;
    $ret1 := $t1;
    $ret2 := $t3;
    return;

    // label L4 at ./sources/market.move:98:5+1
L4:

    // abort($t10) at ./sources/market.move:98:5+1
    $abort_code := $t10;
    $abort_flag := true;
    return;

}

// fun market::get_market_id [baseline] at ./sources/market.move:170:5+95
procedure {:inline 1} $0_market_get_market_id(_$t0: $0_market_Market) returns ($ret0: $2_object_ID)
{
    // declare local variables
    var $t1: $2_object_UID;
    var $t2: $2_object_ID;
    var $t3: int;
    var $t0: $0_market_Market;
    var $temp_0'$0_market_Market': $0_market_Market;
    var $temp_0'$2_object_ID': $2_object_ID;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[market]($t0) at ./sources/market.move:170:5+1
    assume {:print "$at(20,6474,6475)"} true;
    assume {:print "$track_local(15,7,0):", $t0} $t0 == $t0;

    // $t1 := get_field<market::Market>.id($t0) at ./sources/market.move:171:30+10
    assume {:print "$at(20,6552,6562)"} true;
    $t1 := $id#$0_market_Market($t0);

    // $t2 := object::uid_to_inner($t1) on_abort goto L2 with $t3 at ./sources/market.move:171:9+32
    call $t2 := $2_object_uid_to_inner($t1);
    if ($abort_flag) {
        assume {:print "$at(20,6531,6563)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(15,7):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_return[0]($t2) at ./sources/market.move:171:9+32
    assume {:print "$track_return(15,7,0):", $t2} $t2 == $t2;

    // label L1 at ./sources/market.move:172:5+1
    assume {:print "$at(20,6568,6569)"} true;
L1:

    // return $t2 at ./sources/market.move:172:5+1
    $ret0 := $t2;
    return;

    // label L2 at ./sources/market.move:172:5+1
L2:

    // abort($t3) at ./sources/market.move:172:5+1
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun market::get_market_id [verification] at ./sources/market.move:170:5+95
procedure {:timeLimit 40} $0_market_get_market_id$verify(_$t0: $0_market_Market) returns ($ret0: $2_object_ID)
{
    // declare local variables
    var $t1: $2_object_UID;
    var $t2: $2_object_ID;
    var $t3: int;
    var $t0: $0_market_Market;
    var $temp_0'$0_market_Market': $0_market_Market;
    var $temp_0'$2_object_ID': $2_object_ID;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/market.move:170:5+1
    assume {:print "$at(20,6474,6475)"} true;
    assume $IsValid'$0_market_Market'($t0);

    // trace_local[market]($t0) at ./sources/market.move:170:5+1
    assume {:print "$track_local(15,7,0):", $t0} $t0 == $t0;

    // $t1 := get_field<market::Market>.id($t0) at ./sources/market.move:171:30+10
    assume {:print "$at(20,6552,6562)"} true;
    $t1 := $id#$0_market_Market($t0);

    // $t2 := object::uid_to_inner($t1) on_abort goto L2 with $t3 at ./sources/market.move:171:9+32
    call $t2 := $2_object_uid_to_inner($t1);
    if ($abort_flag) {
        assume {:print "$at(20,6531,6563)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(15,7):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_return[0]($t2) at ./sources/market.move:171:9+32
    assume {:print "$track_return(15,7,0):", $t2} $t2 == $t2;

    // label L1 at ./sources/market.move:172:5+1
    assume {:print "$at(20,6568,6569)"} true;
L1:

    // return $t2 at ./sources/market.move:172:5+1
    $ret0 := $t2;
    return;

    // label L2 at ./sources/market.move:172:5+1
L2:

    // abort($t3) at ./sources/market.move:172:5+1
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun market::get_submarket_id<#0> [baseline] at ./sources/market.move:184:5+108
procedure {:inline 1} $0_market_get_submarket_id'#0'(_$t0: $0_market_SubMarket'#0') returns ($ret0: $2_object_ID)
{
    // declare local variables
    var $t1: $2_object_UID;
    var $t2: $2_object_ID;
    var $t3: int;
    var $t0: $0_market_SubMarket'#0';
    var $temp_0'$0_market_SubMarket'#0'': $0_market_SubMarket'#0';
    var $temp_0'$2_object_ID': $2_object_ID;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[sub_market]($t0) at ./sources/market.move:184:5+1
    assume {:print "$at(20,6821,6822)"} true;
    assume {:print "$track_local(15,8,0):", $t0} $t0 == $t0;

    // $t1 := get_field<market::SubMarket<#0>>.id($t0) at ./sources/market.move:185:30+14
    assume {:print "$at(20,6908,6922)"} true;
    $t1 := $id#$0_market_SubMarket'#0'($t0);

    // $t2 := object::uid_to_inner($t1) on_abort goto L2 with $t3 at ./sources/market.move:185:9+36
    call $t2 := $2_object_uid_to_inner($t1);
    if ($abort_flag) {
        assume {:print "$at(20,6887,6923)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(15,8):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_return[0]($t2) at ./sources/market.move:185:9+36
    assume {:print "$track_return(15,8,0):", $t2} $t2 == $t2;

    // label L1 at ./sources/market.move:186:5+1
    assume {:print "$at(20,6928,6929)"} true;
L1:

    // return $t2 at ./sources/market.move:186:5+1
    $ret0 := $t2;
    return;

    // label L2 at ./sources/market.move:186:5+1
L2:

    // abort($t3) at ./sources/market.move:186:5+1
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun market::get_submarket_id<#1> [baseline] at ./sources/market.move:184:5+108
procedure {:inline 1} $0_market_get_submarket_id'#1'(_$t0: $0_market_SubMarket'#1') returns ($ret0: $2_object_ID)
{
    // declare local variables
    var $t1: $2_object_UID;
    var $t2: $2_object_ID;
    var $t3: int;
    var $t0: $0_market_SubMarket'#1';
    var $temp_0'$0_market_SubMarket'#1'': $0_market_SubMarket'#1';
    var $temp_0'$2_object_ID': $2_object_ID;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[sub_market]($t0) at ./sources/market.move:184:5+1
    assume {:print "$at(20,6821,6822)"} true;
    assume {:print "$track_local(15,8,0):", $t0} $t0 == $t0;

    // $t1 := get_field<market::SubMarket<#0>>.id($t0) at ./sources/market.move:185:30+14
    assume {:print "$at(20,6908,6922)"} true;
    $t1 := $id#$0_market_SubMarket'#1'($t0);

    // $t2 := object::uid_to_inner($t1) on_abort goto L2 with $t3 at ./sources/market.move:185:9+36
    call $t2 := $2_object_uid_to_inner($t1);
    if ($abort_flag) {
        assume {:print "$at(20,6887,6923)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(15,8):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_return[0]($t2) at ./sources/market.move:185:9+36
    assume {:print "$track_return(15,8,0):", $t2} $t2 == $t2;

    // label L1 at ./sources/market.move:186:5+1
    assume {:print "$at(20,6928,6929)"} true;
L1:

    // return $t2 at ./sources/market.move:186:5+1
    $ret0 := $t2;
    return;

    // label L2 at ./sources/market.move:186:5+1
L2:

    // abort($t3) at ./sources/market.move:186:5+1
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun market::get_submarket_id [verification] at ./sources/market.move:184:5+108
procedure {:timeLimit 40} $0_market_get_submarket_id$verify(_$t0: $0_market_SubMarket'#0') returns ($ret0: $2_object_ID)
{
    // declare local variables
    var $t1: $2_object_UID;
    var $t2: $2_object_ID;
    var $t3: int;
    var $t0: $0_market_SubMarket'#0';
    var $temp_0'$0_market_SubMarket'#0'': $0_market_SubMarket'#0';
    var $temp_0'$2_object_ID': $2_object_ID;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/market.move:184:5+1
    assume {:print "$at(20,6821,6822)"} true;
    assume $IsValid'$0_market_SubMarket'#0''($t0);

    // trace_local[sub_market]($t0) at ./sources/market.move:184:5+1
    assume {:print "$track_local(15,8,0):", $t0} $t0 == $t0;

    // $t1 := get_field<market::SubMarket<#0>>.id($t0) at ./sources/market.move:185:30+14
    assume {:print "$at(20,6908,6922)"} true;
    $t1 := $id#$0_market_SubMarket'#0'($t0);

    // $t2 := object::uid_to_inner($t1) on_abort goto L2 with $t3 at ./sources/market.move:185:9+36
    call $t2 := $2_object_uid_to_inner($t1);
    if ($abort_flag) {
        assume {:print "$at(20,6887,6923)"} true;
        $t3 := $abort_code;
        assume {:print "$track_abort(15,8):", $t3} $t3 == $t3;
        goto L2;
    }

    // trace_return[0]($t2) at ./sources/market.move:185:9+36
    assume {:print "$track_return(15,8,0):", $t2} $t2 == $t2;

    // label L1 at ./sources/market.move:186:5+1
    assume {:print "$at(20,6928,6929)"} true;
L1:

    // return $t2 at ./sources/market.move:186:5+1
    $ret0 := $t2;
    return;

    // label L2 at ./sources/market.move:186:5+1
L2:

    // abort($t3) at ./sources/market.move:186:5+1
    $abort_code := $t3;
    $abort_flag := true;
    return;

}

// fun market::get_unused_col<#1> [baseline] at ./sources/market.move:188:5+671
procedure {:inline 1} $0_market_get_unused_col'#1'(_$t0: int, _$t1: $0_market_SubMarket'#1') returns ($ret0: int)
{
    // declare local variables
    var $t2: int;
    var $t3: $0_market_ColData;
    var $t4: $2_vec_map_VecMap'address_$0_market_ColData';
    var $t5: bool;
    var $t6: int;
    var $t7: bool;
    var $t8: int;
    var $t9: $2_vec_map_VecMap'address_$0_market_ColData';
    var $t10: $0_market_ColData;
    var $t11: int;
    var $t12: int;
    var $t13: bool;
    var $t14: int;
    var $t15: int;
    var $t16: int;
    var $t17: int;
    var $t18: bool;
    var $t19: int;
    var $t20: int;
    var $t21: int;
    var $t22: int;
    var $t23: bool;
    var $t24: int;
    var $t25: int;
    var $t26: int;
    var $t27: int;
    var $t0: int;
    var $t1: $0_market_SubMarket'#1';
    var $temp_0'$0_market_ColData': $0_market_ColData;
    var $temp_0'$0_market_SubMarket'#1'': $0_market_SubMarket'#1';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[sender]($t0) at ./sources/market.move:188:5+1
    assume {:print "$at(20,6935,6936)"} true;
    assume {:print "$track_local(15,9,0):", $t0} $t0 == $t0;

    // trace_local[sub_market]($t1) at ./sources/market.move:188:5+1
    assume {:print "$track_local(15,9,1):", $t1} $t1 == $t1;

    // $t4 := get_field<market::SubMarket<#0>>.collaterals($t1) at ./sources/market.move:190:31+23
    assume {:print "$at(20,7126,7149)"} true;
    $t4 := $collaterals#$0_market_SubMarket'#1'($t1);

    // $t5 := vec_map::contains<address, market::ColData>($t4, $t0) on_abort goto L11 with $t6 at ./sources/market.move:190:13+50
    call $t5 := $2_vec_map_contains'address_$0_market_ColData'($t4, $t0);
    if ($abort_flag) {
        assume {:print "$at(20,7108,7158)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(15,9):", $t6} $t6 == $t6;
        goto L11;
    }

    // $t7 := !($t5) at ./sources/market.move:190:12+1
    call $t7 := $Not($t5);

    // if ($t7) goto L0 else goto L2 at ./sources/market.move:190:9+496
    if ($t7) { goto L0; } else { goto L2; }

    // label L0 at ./sources/market.move:190:9+496
L0:

    // destroy($t1) at ./sources/market.move:190:9+496

    // destroy($t0) at ./sources/market.move:190:9+496

    // $t8 := 0 at ./sources/market.move:191:13+4
    assume {:print "$at(20,7174,7178)"} true;
    $t8 := 0;
    assume $IsValid'u64'($t8);

    // $t2 := $t8 at ./sources/market.move:190:9+496
    assume {:print "$at(20,7104,7600)"} true;
    $t2 := $t8;

    // goto L3 at ./sources/market.move:190:9+496
    goto L3;

    // label L2 at ./sources/market.move:193:42+10
    assume {:print "$at(20,7237,7247)"} true;
L2:

    // $t9 := get_field<market::SubMarket<#0>>.collaterals($t1) at ./sources/market.move:193:41+23
    $t9 := $collaterals#$0_market_SubMarket'#1'($t1);

    // $t10 := vec_map::get<address, market::ColData>($t9, $t0) on_abort goto L11 with $t6 at ./sources/market.move:193:28+45
    call $t10 := $2_vec_map_get'address_$0_market_ColData'($t9, $t0);
    if ($abort_flag) {
        assume {:print "$at(20,7223,7268)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(15,9):", $t6} $t6 == $t6;
        goto L11;
    }

    // trace_local[col_data]($t10) at ./sources/market.move:193:17+8
    assume {:print "$track_local(15,9,3):", $t10} $t10 == $t10;

    // $t11 := get_field<market::ColData>.gross($t10) at ./sources/market.move:195:21+14
    assume {:print "$at(20,7299,7313)"} true;
    $t11 := $gross#$0_market_ColData($t10);

    // $t12 := get_field<market::ColData>.utilized($t10) at ./sources/market.move:195:39+17
    $t12 := $utilized#$0_market_ColData($t10);

    // $t13 := >=($t11, $t12) at ./sources/market.move:195:36+2
    call $t13 := $Ge($t11, $t12);

    // if ($t13) goto L4 else goto L5 at ./sources/market.move:195:13+84
    if ($t13) { goto L4; } else { goto L5; }

    // label L5 at ./sources/market.move:195:13+84
L5:

    // destroy($t10) at ./sources/market.move:195:13+84

    // $t14 := 4 at ./sources/market.move:195:80+15
    $t14 := 4;
    assume $IsValid'u64'($t14);

    // $t15 := opaque begin: errors::invalid_state($t14) at ./sources/market.move:195:58+38

    // assume WellFormed($t15) at ./sources/market.move:195:58+38
    assume $IsValid'u64'($t15);

    // assume Eq<u64>($t15, 1) at ./sources/market.move:195:58+38
    assume $IsEqual'u64'($t15, 1);

    // $t15 := opaque end: errors::invalid_state($t14) at ./sources/market.move:195:58+38

    // trace_abort($t15) at ./sources/market.move:195:13+84
    assume {:print "$at(20,7291,7375)"} true;
    assume {:print "$track_abort(15,9):", $t15} $t15 == $t15;

    // $t6 := move($t15) at ./sources/market.move:195:13+84
    $t6 := $t15;

    // goto L11 at ./sources/market.move:195:13+84
    goto L11;

    // label L4 at ./sources/market.move:196:21+8
    assume {:print "$at(20,7397,7405)"} true;
L4:

    // $t16 := get_field<market::ColData>.gross($t10) at ./sources/market.move:196:21+14
    $t16 := $gross#$0_market_ColData($t10);

    // $t17 := 0 at ./sources/market.move:196:38+1
    $t17 := 0;
    assume $IsValid'u64'($t17);

    // $t18 := >($t16, $t17) at ./sources/market.move:196:36+1
    call $t18 := $Gt($t16, $t17);

    // if ($t18) goto L6 else goto L7 at ./sources/market.move:196:13+67
    if ($t18) { goto L6; } else { goto L7; }

    // label L7 at ./sources/market.move:196:13+67
L7:

    // destroy($t10) at ./sources/market.move:196:13+67

    // $t19 := 4 at ./sources/market.move:196:63+15
    $t19 := 4;
    assume $IsValid'u64'($t19);

    // $t20 := opaque begin: errors::invalid_state($t19) at ./sources/market.move:196:41+38

    // assume WellFormed($t20) at ./sources/market.move:196:41+38
    assume $IsValid'u64'($t20);

    // assume Eq<u64>($t20, 1) at ./sources/market.move:196:41+38
    assume $IsEqual'u64'($t20, 1);

    // $t20 := opaque end: errors::invalid_state($t19) at ./sources/market.move:196:41+38

    // trace_abort($t20) at ./sources/market.move:196:13+67
    assume {:print "$at(20,7389,7456)"} true;
    assume {:print "$track_abort(15,9):", $t20} $t20 == $t20;

    // $t6 := move($t20) at ./sources/market.move:196:13+67
    $t6 := $t20;

    // goto L11 at ./sources/market.move:196:13+67
    goto L11;

    // label L6 at ./sources/market.move:197:21+8
    assume {:print "$at(20,7478,7486)"} true;
L6:

    // $t21 := get_field<market::ColData>.utilized($t10) at ./sources/market.move:197:21+17
    $t21 := $utilized#$0_market_ColData($t10);

    // $t22 := 0 at ./sources/market.move:197:42+1
    $t22 := 0;
    assume $IsValid'u64'($t22);

    // $t23 := >=($t21, $t22) at ./sources/market.move:197:39+2
    call $t23 := $Ge($t21, $t22);

    // if ($t23) goto L8 else goto L9 at ./sources/market.move:197:13+71
    if ($t23) { goto L8; } else { goto L9; }

    // label L9 at ./sources/market.move:197:13+71
L9:

    // destroy($t10) at ./sources/market.move:197:13+71

    // $t24 := 4 at ./sources/market.move:197:67+15
    $t24 := 4;
    assume $IsValid'u64'($t24);

    // $t25 := opaque begin: errors::invalid_state($t24) at ./sources/market.move:197:45+38

    // assume WellFormed($t25) at ./sources/market.move:197:45+38
    assume $IsValid'u64'($t25);

    // assume Eq<u64>($t25, 1) at ./sources/market.move:197:45+38
    assume $IsEqual'u64'($t25, 1);

    // $t25 := opaque end: errors::invalid_state($t24) at ./sources/market.move:197:45+38

    // trace_abort($t25) at ./sources/market.move:197:13+71
    assume {:print "$at(20,7470,7541)"} true;
    assume {:print "$track_abort(15,9):", $t25} $t25 == $t25;

    // $t6 := move($t25) at ./sources/market.move:197:13+71
    $t6 := $t25;

    // goto L11 at ./sources/market.move:197:13+71
    goto L11;

    // label L8 at ./sources/market.move:199:13+8
    assume {:print "$at(20,7556,7564)"} true;
L8:

    // $t26 := get_field<market::ColData>.gross($t10) at ./sources/market.move:199:13+14
    $t26 := $gross#$0_market_ColData($t10);

    // $t27 := get_field<market::ColData>.utilized($t10) at ./sources/market.move:199:30+17
    $t27 := $utilized#$0_market_ColData($t10);

    // $t2 := -($t26, $t27) on_abort goto L11 with $t6 at ./sources/market.move:199:28+1
    call $t2 := $Sub($t26, $t27);
    if ($abort_flag) {
        assume {:print "$at(20,7571,7572)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(15,9):", $t6} $t6 == $t6;
        goto L11;
    }

    // label L3 at ./sources/market.move:190:9+496
    assume {:print "$at(20,7104,7600)"} true;
L3:

    // trace_return[0]($t2) at ./sources/market.move:190:9+496
    assume {:print "$track_return(15,9,0):", $t2} $t2 == $t2;

    // label L10 at ./sources/market.move:201:5+1
    assume {:print "$at(20,7605,7606)"} true;
L10:

    // return $t2 at ./sources/market.move:201:5+1
    $ret0 := $t2;
    return;

    // label L11 at ./sources/market.move:201:5+1
L11:

    // abort($t6) at ./sources/market.move:201:5+1
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun market::get_unused_col [verification] at ./sources/market.move:188:5+671
procedure {:timeLimit 40} $0_market_get_unused_col$verify(_$t0: int, _$t1: $0_market_SubMarket'#0') returns ($ret0: int)
{
    // declare local variables
    var $t2: int;
    var $t3: $0_market_ColData;
    var $t4: $2_vec_map_VecMap'address_$0_market_ColData';
    var $t5: bool;
    var $t6: int;
    var $t7: bool;
    var $t8: int;
    var $t9: $2_vec_map_VecMap'address_$0_market_ColData';
    var $t10: $0_market_ColData;
    var $t11: int;
    var $t12: int;
    var $t13: bool;
    var $t14: int;
    var $t15: int;
    var $t16: int;
    var $t17: int;
    var $t18: bool;
    var $t19: int;
    var $t20: int;
    var $t21: int;
    var $t22: int;
    var $t23: bool;
    var $t24: int;
    var $t25: int;
    var $t26: int;
    var $t27: int;
    var $t0: int;
    var $t1: $0_market_SubMarket'#0';
    var $temp_0'$0_market_ColData': $0_market_ColData;
    var $temp_0'$0_market_SubMarket'#0'': $0_market_SubMarket'#0';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/market.move:188:5+1
    assume {:print "$at(20,6935,6936)"} true;
    assume $IsValid'address'($t0);

    // assume WellFormed($t1) at ./sources/market.move:188:5+1
    assume $IsValid'$0_market_SubMarket'#0''($t1);

    // trace_local[sender]($t0) at ./sources/market.move:188:5+1
    assume {:print "$track_local(15,9,0):", $t0} $t0 == $t0;

    // trace_local[sub_market]($t1) at ./sources/market.move:188:5+1
    assume {:print "$track_local(15,9,1):", $t1} $t1 == $t1;

    // $t4 := get_field<market::SubMarket<#0>>.collaterals($t1) at ./sources/market.move:190:31+23
    assume {:print "$at(20,7126,7149)"} true;
    $t4 := $collaterals#$0_market_SubMarket'#0'($t1);

    // $t5 := vec_map::contains<address, market::ColData>($t4, $t0) on_abort goto L11 with $t6 at ./sources/market.move:190:13+50
    call $t5 := $2_vec_map_contains'address_$0_market_ColData'($t4, $t0);
    if ($abort_flag) {
        assume {:print "$at(20,7108,7158)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(15,9):", $t6} $t6 == $t6;
        goto L11;
    }

    // $t7 := !($t5) at ./sources/market.move:190:12+1
    call $t7 := $Not($t5);

    // if ($t7) goto L0 else goto L2 at ./sources/market.move:190:9+496
    if ($t7) { goto L0; } else { goto L2; }

    // label L0 at ./sources/market.move:190:9+496
L0:

    // destroy($t1) at ./sources/market.move:190:9+496

    // destroy($t0) at ./sources/market.move:190:9+496

    // $t8 := 0 at ./sources/market.move:191:13+4
    assume {:print "$at(20,7174,7178)"} true;
    $t8 := 0;
    assume $IsValid'u64'($t8);

    // $t2 := $t8 at ./sources/market.move:190:9+496
    assume {:print "$at(20,7104,7600)"} true;
    $t2 := $t8;

    // goto L3 at ./sources/market.move:190:9+496
    goto L3;

    // label L2 at ./sources/market.move:193:42+10
    assume {:print "$at(20,7237,7247)"} true;
L2:

    // $t9 := get_field<market::SubMarket<#0>>.collaterals($t1) at ./sources/market.move:193:41+23
    $t9 := $collaterals#$0_market_SubMarket'#0'($t1);

    // $t10 := vec_map::get<address, market::ColData>($t9, $t0) on_abort goto L11 with $t6 at ./sources/market.move:193:28+45
    call $t10 := $2_vec_map_get'address_$0_market_ColData'($t9, $t0);
    if ($abort_flag) {
        assume {:print "$at(20,7223,7268)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(15,9):", $t6} $t6 == $t6;
        goto L11;
    }

    // trace_local[col_data]($t10) at ./sources/market.move:193:17+8
    assume {:print "$track_local(15,9,3):", $t10} $t10 == $t10;

    // $t11 := get_field<market::ColData>.gross($t10) at ./sources/market.move:195:21+14
    assume {:print "$at(20,7299,7313)"} true;
    $t11 := $gross#$0_market_ColData($t10);

    // $t12 := get_field<market::ColData>.utilized($t10) at ./sources/market.move:195:39+17
    $t12 := $utilized#$0_market_ColData($t10);

    // $t13 := >=($t11, $t12) at ./sources/market.move:195:36+2
    call $t13 := $Ge($t11, $t12);

    // if ($t13) goto L4 else goto L5 at ./sources/market.move:195:13+84
    if ($t13) { goto L4; } else { goto L5; }

    // label L5 at ./sources/market.move:195:13+84
L5:

    // destroy($t10) at ./sources/market.move:195:13+84

    // $t14 := 4 at ./sources/market.move:195:80+15
    $t14 := 4;
    assume $IsValid'u64'($t14);

    // $t15 := opaque begin: errors::invalid_state($t14) at ./sources/market.move:195:58+38

    // assume WellFormed($t15) at ./sources/market.move:195:58+38
    assume $IsValid'u64'($t15);

    // assume Eq<u64>($t15, 1) at ./sources/market.move:195:58+38
    assume $IsEqual'u64'($t15, 1);

    // $t15 := opaque end: errors::invalid_state($t14) at ./sources/market.move:195:58+38

    // trace_abort($t15) at ./sources/market.move:195:13+84
    assume {:print "$at(20,7291,7375)"} true;
    assume {:print "$track_abort(15,9):", $t15} $t15 == $t15;

    // $t6 := move($t15) at ./sources/market.move:195:13+84
    $t6 := $t15;

    // goto L11 at ./sources/market.move:195:13+84
    goto L11;

    // label L4 at ./sources/market.move:196:21+8
    assume {:print "$at(20,7397,7405)"} true;
L4:

    // $t16 := get_field<market::ColData>.gross($t10) at ./sources/market.move:196:21+14
    $t16 := $gross#$0_market_ColData($t10);

    // $t17 := 0 at ./sources/market.move:196:38+1
    $t17 := 0;
    assume $IsValid'u64'($t17);

    // $t18 := >($t16, $t17) at ./sources/market.move:196:36+1
    call $t18 := $Gt($t16, $t17);

    // if ($t18) goto L6 else goto L7 at ./sources/market.move:196:13+67
    if ($t18) { goto L6; } else { goto L7; }

    // label L7 at ./sources/market.move:196:13+67
L7:

    // destroy($t10) at ./sources/market.move:196:13+67

    // $t19 := 4 at ./sources/market.move:196:63+15
    $t19 := 4;
    assume $IsValid'u64'($t19);

    // $t20 := opaque begin: errors::invalid_state($t19) at ./sources/market.move:196:41+38

    // assume WellFormed($t20) at ./sources/market.move:196:41+38
    assume $IsValid'u64'($t20);

    // assume Eq<u64>($t20, 1) at ./sources/market.move:196:41+38
    assume $IsEqual'u64'($t20, 1);

    // $t20 := opaque end: errors::invalid_state($t19) at ./sources/market.move:196:41+38

    // trace_abort($t20) at ./sources/market.move:196:13+67
    assume {:print "$at(20,7389,7456)"} true;
    assume {:print "$track_abort(15,9):", $t20} $t20 == $t20;

    // $t6 := move($t20) at ./sources/market.move:196:13+67
    $t6 := $t20;

    // goto L11 at ./sources/market.move:196:13+67
    goto L11;

    // label L6 at ./sources/market.move:197:21+8
    assume {:print "$at(20,7478,7486)"} true;
L6:

    // $t21 := get_field<market::ColData>.utilized($t10) at ./sources/market.move:197:21+17
    $t21 := $utilized#$0_market_ColData($t10);

    // $t22 := 0 at ./sources/market.move:197:42+1
    $t22 := 0;
    assume $IsValid'u64'($t22);

    // $t23 := >=($t21, $t22) at ./sources/market.move:197:39+2
    call $t23 := $Ge($t21, $t22);

    // if ($t23) goto L8 else goto L9 at ./sources/market.move:197:13+71
    if ($t23) { goto L8; } else { goto L9; }

    // label L9 at ./sources/market.move:197:13+71
L9:

    // destroy($t10) at ./sources/market.move:197:13+71

    // $t24 := 4 at ./sources/market.move:197:67+15
    $t24 := 4;
    assume $IsValid'u64'($t24);

    // $t25 := opaque begin: errors::invalid_state($t24) at ./sources/market.move:197:45+38

    // assume WellFormed($t25) at ./sources/market.move:197:45+38
    assume $IsValid'u64'($t25);

    // assume Eq<u64>($t25, 1) at ./sources/market.move:197:45+38
    assume $IsEqual'u64'($t25, 1);

    // $t25 := opaque end: errors::invalid_state($t24) at ./sources/market.move:197:45+38

    // trace_abort($t25) at ./sources/market.move:197:13+71
    assume {:print "$at(20,7470,7541)"} true;
    assume {:print "$track_abort(15,9):", $t25} $t25 == $t25;

    // $t6 := move($t25) at ./sources/market.move:197:13+71
    $t6 := $t25;

    // goto L11 at ./sources/market.move:197:13+71
    goto L11;

    // label L8 at ./sources/market.move:199:13+8
    assume {:print "$at(20,7556,7564)"} true;
L8:

    // $t26 := get_field<market::ColData>.gross($t10) at ./sources/market.move:199:13+14
    $t26 := $gross#$0_market_ColData($t10);

    // $t27 := get_field<market::ColData>.utilized($t10) at ./sources/market.move:199:30+17
    $t27 := $utilized#$0_market_ColData($t10);

    // $t2 := -($t26, $t27) on_abort goto L11 with $t6 at ./sources/market.move:199:28+1
    call $t2 := $Sub($t26, $t27);
    if ($abort_flag) {
        assume {:print "$at(20,7571,7572)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(15,9):", $t6} $t6 == $t6;
        goto L11;
    }

    // label L3 at ./sources/market.move:190:9+496
    assume {:print "$at(20,7104,7600)"} true;
L3:

    // trace_return[0]($t2) at ./sources/market.move:190:9+496
    assume {:print "$track_return(15,9,0):", $t2} $t2 == $t2;

    // label L10 at ./sources/market.move:201:5+1
    assume {:print "$at(20,7605,7606)"} true;
L10:

    // return $t2 at ./sources/market.move:201:5+1
    $ret0 := $t2;
    return;

    // label L11 at ./sources/market.move:201:5+1
L11:

    // abort($t6) at ./sources/market.move:201:5+1
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun market::record_new_utilization [baseline] at ./sources/market.move:161:5+448
procedure {:inline 1} $0_market_record_new_utilization(_$t0: $Mutation ($2_vec_map_VecMap'address_$0_market_ColData'), _$t1: int, _$t2: int) returns ($ret0: $Mutation ($2_vec_map_VecMap'address_$0_market_ColData'))
{
    // declare local variables
    var $t3: $Mutation ($2_vec_map_VecMap'address_$0_market_ColData');
    var $t4: int;
    var $t5: $Mutation ($0_market_ColData);
    var $t6: $2_vec_map_VecMap'address_$0_market_ColData';
    var $t7: bool;
    var $t8: int;
    var $t9: bool;
    var $t10: bool;
    var $t11: int;
    var $t12: int;
    var $t13: $Mutation ($0_market_ColData);
    var $t14: int;
    var $t15: int;
    var $t16: int;
    var $t17: bool;
    var $t18: int;
    var $t19: int;
    var $t20: int;
    var $t21: int;
    var $t22: $Mutation (int);
    var $t0: $Mutation ($2_vec_map_VecMap'address_$0_market_ColData');
    var $t1: int;
    var $t2: int;
    var $temp_0'$0_market_ColData': $0_market_ColData;
    var $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'': $2_vec_map_VecMap'address_$0_market_ColData';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;
    assume IsEmptyVec(p#$Mutation($t3));
    assume IsEmptyVec(p#$Mutation($t5));
    assume IsEmptyVec(p#$Mutation($t13));
    assume IsEmptyVec(p#$Mutation($t22));

    // bytecode translation starts here
    // trace_local[collaterals]($t0) at ./sources/market.move:161:5+1
    assume {:print "$at(20,5996,5997)"} true;
    $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' := $Dereference($t0);
    assume {:print "$track_local(15,10,0):", $temp_0'$2_vec_map_VecMap'address_$0_market_ColData''} $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' == $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'';

    // trace_local[sender]($t1) at ./sources/market.move:161:5+1
    assume {:print "$track_local(15,10,1):", $t1} $t1 == $t1;

    // trace_local[value]($t2) at ./sources/market.move:161:5+1
    assume {:print "$track_local(15,10,2):", $t2} $t2 == $t2;

    // $t6 := read_ref($t0) at ./sources/market.move:162:34+21
    assume {:print "$at(20,6132,6153)"} true;
    $t6 := $Dereference($t0);

    // $t7 := vec_map::contains<address, market::ColData>($t6, $t1) on_abort goto L6 with $t8 at ./sources/market.move:162:17+38
    call $t7 := $2_vec_map_contains'address_$0_market_ColData'($t6, $t1);
    if ($abort_flag) {
        assume {:print "$at(20,6115,6153)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(15,10):", $t8} $t8 == $t8;
        goto L6;
    }

    // $t9 := true at ./sources/market.move:162:59+4
    $t9 := true;
    assume $IsValid'bool'($t9);

    // $t10 := ==($t7, $t9) at ./sources/market.move:162:56+2
    $t10 := $IsEqual'bool'($t7, $t9);

    // if ($t10) goto L0 else goto L1 at ./sources/market.move:162:9+97
    if ($t10) { goto L0; } else { goto L1; }

    // label L1 at ./sources/market.move:162:9+97
L1:

    // destroy($t1) at ./sources/market.move:162:9+97

    // destroy($t0) at ./sources/market.move:162:9+97

    // $t11 := 8 at ./sources/market.move:162:90+14
    $t11 := 8;
    assume $IsValid'u64'($t11);

    // $t12 := opaque begin: errors::invalid_argument($t11) at ./sources/market.move:162:65+40

    // assume WellFormed($t12) at ./sources/market.move:162:65+40
    assume $IsValid'u64'($t12);

    // assume Eq<u64>($t12, 7) at ./sources/market.move:162:65+40
    assume $IsEqual'u64'($t12, 7);

    // $t12 := opaque end: errors::invalid_argument($t11) at ./sources/market.move:162:65+40

    // trace_abort($t12) at ./sources/market.move:162:9+97
    assume {:print "$at(20,6107,6204)"} true;
    assume {:print "$track_abort(15,10):", $t12} $t12 == $t12;

    // $t8 := move($t12) at ./sources/market.move:162:9+97
    $t8 := $t12;

    // goto L6 at ./sources/market.move:162:9+97
    goto L6;

    // label L0 at ./sources/market.move:163:41+11
    assume {:print "$at(20,6246,6257)"} true;
L0:

    // $t13 := vec_map::get_mut<address, market::ColData>($t0, $t1) on_abort goto L6 with $t8 at ./sources/market.move:163:24+37
    call $t13,$t0 := $2_vec_map_get_mut'address_$0_market_ColData'($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(20,6229,6266)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(15,10):", $t8} $t8 == $t8;
        goto L6;
    }

    // trace_local[col_data]($t13) at ./sources/market.move:163:13+8
    $temp_0'$0_market_ColData' := $Dereference($t13);
    assume {:print "$track_local(15,10,5):", $temp_0'$0_market_ColData'} $temp_0'$0_market_ColData' == $temp_0'$0_market_ColData';

    // $t14 := get_field<market::ColData>.gross($t13) at ./sources/market.move:165:17+14
    assume {:print "$at(20,6293,6307)"} true;
    $t14 := $gross#$0_market_ColData($Dereference($t13));

    // $t15 := get_field<market::ColData>.utilized($t13) at ./sources/market.move:165:43+17
    $t15 := $utilized#$0_market_ColData($Dereference($t13));

    // $t16 := +($t2, $t15) on_abort goto L6 with $t8 at ./sources/market.move:165:41+1
    call $t16 := $AddU64($t2, $t15);
    if ($abort_flag) {
        assume {:print "$at(20,6317,6318)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(15,10):", $t8} $t8 == $t8;
        goto L6;
    }

    // $t17 := >=($t14, $t16) at ./sources/market.move:165:32+2
    call $t17 := $Ge($t14, $t16);

    // if ($t17) goto L2 else goto L4 at ./sources/market.move:165:9+97
    if ($t17) { goto L2; } else { goto L4; }

    // label L3 at ./sources/market.move:165:9+97
L3:

    // trace_local[collaterals]($t0) at ./sources/market.move:165:9+97
    $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' := $Dereference($t0);
    assume {:print "$track_local(15,10,0):", $temp_0'$2_vec_map_VecMap'address_$0_market_ColData''} $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' == $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'';

    // destroy($t13) at ./sources/market.move:165:9+97

    // $t18 := 6 at ./sources/market.move:165:87+17
    $t18 := 6;
    assume $IsValid'u64'($t18);

    // $t19 := opaque begin: errors::invalid_argument($t18) at ./sources/market.move:165:62+43

    // assume WellFormed($t19) at ./sources/market.move:165:62+43
    assume $IsValid'u64'($t19);

    // assume Eq<u64>($t19, 7) at ./sources/market.move:165:62+43
    assume $IsEqual'u64'($t19, 7);

    // $t19 := opaque end: errors::invalid_argument($t18) at ./sources/market.move:165:62+43

    // trace_abort($t19) at ./sources/market.move:165:9+97
    assume {:print "$at(20,6285,6382)"} true;
    assume {:print "$track_abort(15,10):", $t19} $t19 == $t19;

    // $t8 := move($t19) at ./sources/market.move:165:9+97
    $t8 := $t19;

    // goto L6 at ./sources/market.move:165:9+97
    goto L6;

    // label L2 at ./sources/market.move:166:29+8
    assume {:print "$at(20,6412,6420)"} true;
L2:

    // $t20 := get_field<market::ColData>.utilized($t13) at ./sources/market.move:166:29+17
    $t20 := $utilized#$0_market_ColData($Dereference($t13));

    // $t21 := +($t20, $t2) on_abort goto L6 with $t8 at ./sources/market.move:166:47+1
    call $t21 := $AddU64($t20, $t2);
    if ($abort_flag) {
        assume {:print "$at(20,6430,6431)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(15,10):", $t8} $t8 == $t8;
        goto L6;
    }

    // $t22 := borrow_field<market::ColData>.utilized($t13) at ./sources/market.move:166:9+17
    $t22 := $ChildMutation($t13, 1, $utilized#$0_market_ColData($Dereference($t13)));

    // write_ref($t22, $t21) at ./sources/market.move:166:9+45
    $t22 := $UpdateMutation($t22, $t21);

    // write_back[Reference($t13).utilized (u64)]($t22) at ./sources/market.move:166:9+45
    $t13 := $UpdateMutation($t13, $Update'$0_market_ColData'_utilized($Dereference($t13), $Dereference($t22)));

    // write_back[Reference($t0).contents (vector<vec_map::Entry<address, market::ColData>>)/[]/.value (market::ColData)]($t13) at ./sources/market.move:166:9+45
    $t0 := $UpdateMutation($t0, (var $$sel0 := $contents#$2_vec_map_VecMap'address_$0_market_ColData'($Dereference($t0)); $Update'$2_vec_map_VecMap'address_$0_market_ColData''_contents($Dereference($t0), (var $$sel1 := ReadVec($$sel0, ReadVec(p#$Mutation($t13), LenVec(p#$Mutation($t0)) + 1)); UpdateVec($$sel0, ReadVec(p#$Mutation($t13), LenVec(p#$Mutation($t0)) + 1), $Update'$2_vec_map_Entry'address_$0_market_ColData''_value($$sel1, $Dereference($t13)))))));

    // trace_local[collaterals]($t0) at ./sources/market.move:166:9+45
    $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' := $Dereference($t0);
    assume {:print "$track_local(15,10,0):", $temp_0'$2_vec_map_VecMap'address_$0_market_ColData''} $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' == $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'';

    // trace_local[collaterals]($t0) at ./sources/market.move:166:54+1
    $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' := $Dereference($t0);
    assume {:print "$track_local(15,10,0):", $temp_0'$2_vec_map_VecMap'address_$0_market_ColData''} $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' == $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'';

    // goto L5 at ./sources/market.move:166:54+1
    goto L5;

    // label L4 at <internal>:1:1+10
    assume {:print "$at(1,0,10)"} true;
L4:

    // destroy($t0) at <internal>:1:1+10

    // goto L3 at <internal>:1:1+10
    goto L3;

    // label L5 at ./sources/market.move:167:5+1
    assume {:print "$at(20,6443,6444)"} true;
L5:

    // return () at ./sources/market.move:167:5+1
    $ret0 := $t0;
    return;

    // label L6 at ./sources/market.move:167:5+1
L6:

    // abort($t8) at ./sources/market.move:167:5+1
    $abort_code := $t8;
    $abort_flag := true;
    return;

}

// fun market::record_new_utilization [verification] at ./sources/market.move:161:5+448
procedure {:timeLimit 40} $0_market_record_new_utilization$verify(_$t0: $Mutation ($2_vec_map_VecMap'address_$0_market_ColData'), _$t1: int, _$t2: int) returns ($ret0: $Mutation ($2_vec_map_VecMap'address_$0_market_ColData'))
{
    // declare local variables
    var $t3: $Mutation ($2_vec_map_VecMap'address_$0_market_ColData');
    var $t4: int;
    var $t5: $Mutation ($0_market_ColData);
    var $t6: $2_vec_map_VecMap'address_$0_market_ColData';
    var $t7: bool;
    var $t8: int;
    var $t9: bool;
    var $t10: bool;
    var $t11: int;
    var $t12: int;
    var $t13: $Mutation ($0_market_ColData);
    var $t14: int;
    var $t15: int;
    var $t16: int;
    var $t17: bool;
    var $t18: int;
    var $t19: int;
    var $t20: int;
    var $t21: int;
    var $t22: $Mutation (int);
    var $t0: $Mutation ($2_vec_map_VecMap'address_$0_market_ColData');
    var $t1: int;
    var $t2: int;
    var $temp_0'$0_market_ColData': $0_market_ColData;
    var $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'': $2_vec_map_VecMap'address_$0_market_ColData';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;
    assume IsEmptyVec(p#$Mutation($t3));
    assume IsEmptyVec(p#$Mutation($t5));
    assume IsEmptyVec(p#$Mutation($t13));
    assume IsEmptyVec(p#$Mutation($t22));

    // verification entrypoint assumptions
    call $InitVerification();
    assume l#$Mutation($t0) == $Param(0);

    // bytecode translation starts here
    // assume WellFormed($t0) at ./sources/market.move:161:5+1
    assume {:print "$at(20,5996,5997)"} true;
    assume $IsValid'$2_vec_map_VecMap'address_$0_market_ColData''($Dereference($t0));

    // assume WellFormed($t1) at ./sources/market.move:161:5+1
    assume $IsValid'address'($t1);

    // assume WellFormed($t2) at ./sources/market.move:161:5+1
    assume $IsValid'u64'($t2);

    // trace_local[collaterals]($t0) at ./sources/market.move:161:5+1
    $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' := $Dereference($t0);
    assume {:print "$track_local(15,10,0):", $temp_0'$2_vec_map_VecMap'address_$0_market_ColData''} $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' == $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'';

    // trace_local[sender]($t1) at ./sources/market.move:161:5+1
    assume {:print "$track_local(15,10,1):", $t1} $t1 == $t1;

    // trace_local[value]($t2) at ./sources/market.move:161:5+1
    assume {:print "$track_local(15,10,2):", $t2} $t2 == $t2;

    // $t6 := read_ref($t0) at ./sources/market.move:162:34+21
    assume {:print "$at(20,6132,6153)"} true;
    $t6 := $Dereference($t0);

    // $t7 := vec_map::contains<address, market::ColData>($t6, $t1) on_abort goto L6 with $t8 at ./sources/market.move:162:17+38
    call $t7 := $2_vec_map_contains'address_$0_market_ColData'($t6, $t1);
    if ($abort_flag) {
        assume {:print "$at(20,6115,6153)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(15,10):", $t8} $t8 == $t8;
        goto L6;
    }

    // $t9 := true at ./sources/market.move:162:59+4
    $t9 := true;
    assume $IsValid'bool'($t9);

    // $t10 := ==($t7, $t9) at ./sources/market.move:162:56+2
    $t10 := $IsEqual'bool'($t7, $t9);

    // if ($t10) goto L0 else goto L1 at ./sources/market.move:162:9+97
    if ($t10) { goto L0; } else { goto L1; }

    // label L1 at ./sources/market.move:162:9+97
L1:

    // destroy($t1) at ./sources/market.move:162:9+97

    // destroy($t0) at ./sources/market.move:162:9+97

    // $t11 := 8 at ./sources/market.move:162:90+14
    $t11 := 8;
    assume $IsValid'u64'($t11);

    // $t12 := opaque begin: errors::invalid_argument($t11) at ./sources/market.move:162:65+40

    // assume WellFormed($t12) at ./sources/market.move:162:65+40
    assume $IsValid'u64'($t12);

    // assume Eq<u64>($t12, 7) at ./sources/market.move:162:65+40
    assume $IsEqual'u64'($t12, 7);

    // $t12 := opaque end: errors::invalid_argument($t11) at ./sources/market.move:162:65+40

    // trace_abort($t12) at ./sources/market.move:162:9+97
    assume {:print "$at(20,6107,6204)"} true;
    assume {:print "$track_abort(15,10):", $t12} $t12 == $t12;

    // $t8 := move($t12) at ./sources/market.move:162:9+97
    $t8 := $t12;

    // goto L6 at ./sources/market.move:162:9+97
    goto L6;

    // label L0 at ./sources/market.move:163:41+11
    assume {:print "$at(20,6246,6257)"} true;
L0:

    // $t13 := vec_map::get_mut<address, market::ColData>($t0, $t1) on_abort goto L6 with $t8 at ./sources/market.move:163:24+37
    call $t13,$t0 := $2_vec_map_get_mut'address_$0_market_ColData'($t0, $t1);
    if ($abort_flag) {
        assume {:print "$at(20,6229,6266)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(15,10):", $t8} $t8 == $t8;
        goto L6;
    }

    // trace_local[col_data]($t13) at ./sources/market.move:163:13+8
    $temp_0'$0_market_ColData' := $Dereference($t13);
    assume {:print "$track_local(15,10,5):", $temp_0'$0_market_ColData'} $temp_0'$0_market_ColData' == $temp_0'$0_market_ColData';

    // $t14 := get_field<market::ColData>.gross($t13) at ./sources/market.move:165:17+14
    assume {:print "$at(20,6293,6307)"} true;
    $t14 := $gross#$0_market_ColData($Dereference($t13));

    // $t15 := get_field<market::ColData>.utilized($t13) at ./sources/market.move:165:43+17
    $t15 := $utilized#$0_market_ColData($Dereference($t13));

    // $t16 := +($t2, $t15) on_abort goto L6 with $t8 at ./sources/market.move:165:41+1
    call $t16 := $AddU64($t2, $t15);
    if ($abort_flag) {
        assume {:print "$at(20,6317,6318)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(15,10):", $t8} $t8 == $t8;
        goto L6;
    }

    // $t17 := >=($t14, $t16) at ./sources/market.move:165:32+2
    call $t17 := $Ge($t14, $t16);

    // if ($t17) goto L2 else goto L4 at ./sources/market.move:165:9+97
    if ($t17) { goto L2; } else { goto L4; }

    // label L3 at ./sources/market.move:165:9+97
L3:

    // trace_local[collaterals]($t0) at ./sources/market.move:165:9+97
    $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' := $Dereference($t0);
    assume {:print "$track_local(15,10,0):", $temp_0'$2_vec_map_VecMap'address_$0_market_ColData''} $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' == $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'';

    // destroy($t13) at ./sources/market.move:165:9+97

    // $t18 := 6 at ./sources/market.move:165:87+17
    $t18 := 6;
    assume $IsValid'u64'($t18);

    // $t19 := opaque begin: errors::invalid_argument($t18) at ./sources/market.move:165:62+43

    // assume WellFormed($t19) at ./sources/market.move:165:62+43
    assume $IsValid'u64'($t19);

    // assume Eq<u64>($t19, 7) at ./sources/market.move:165:62+43
    assume $IsEqual'u64'($t19, 7);

    // $t19 := opaque end: errors::invalid_argument($t18) at ./sources/market.move:165:62+43

    // trace_abort($t19) at ./sources/market.move:165:9+97
    assume {:print "$at(20,6285,6382)"} true;
    assume {:print "$track_abort(15,10):", $t19} $t19 == $t19;

    // $t8 := move($t19) at ./sources/market.move:165:9+97
    $t8 := $t19;

    // goto L6 at ./sources/market.move:165:9+97
    goto L6;

    // label L2 at ./sources/market.move:166:29+8
    assume {:print "$at(20,6412,6420)"} true;
L2:

    // $t20 := get_field<market::ColData>.utilized($t13) at ./sources/market.move:166:29+17
    $t20 := $utilized#$0_market_ColData($Dereference($t13));

    // $t21 := +($t20, $t2) on_abort goto L6 with $t8 at ./sources/market.move:166:47+1
    call $t21 := $AddU64($t20, $t2);
    if ($abort_flag) {
        assume {:print "$at(20,6430,6431)"} true;
        $t8 := $abort_code;
        assume {:print "$track_abort(15,10):", $t8} $t8 == $t8;
        goto L6;
    }

    // $t22 := borrow_field<market::ColData>.utilized($t13) at ./sources/market.move:166:9+17
    $t22 := $ChildMutation($t13, 1, $utilized#$0_market_ColData($Dereference($t13)));

    // write_ref($t22, $t21) at ./sources/market.move:166:9+45
    $t22 := $UpdateMutation($t22, $t21);

    // write_back[Reference($t13).utilized (u64)]($t22) at ./sources/market.move:166:9+45
    $t13 := $UpdateMutation($t13, $Update'$0_market_ColData'_utilized($Dereference($t13), $Dereference($t22)));

    // write_back[Reference($t0).contents (vector<vec_map::Entry<address, market::ColData>>)/[]/.value (market::ColData)]($t13) at ./sources/market.move:166:9+45
    $t0 := $UpdateMutation($t0, (var $$sel0 := $contents#$2_vec_map_VecMap'address_$0_market_ColData'($Dereference($t0)); $Update'$2_vec_map_VecMap'address_$0_market_ColData''_contents($Dereference($t0), (var $$sel1 := ReadVec($$sel0, ReadVec(p#$Mutation($t13), LenVec(p#$Mutation($t0)) + 1)); UpdateVec($$sel0, ReadVec(p#$Mutation($t13), LenVec(p#$Mutation($t0)) + 1), $Update'$2_vec_map_Entry'address_$0_market_ColData''_value($$sel1, $Dereference($t13)))))));

    // trace_local[collaterals]($t0) at ./sources/market.move:166:9+45
    $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' := $Dereference($t0);
    assume {:print "$track_local(15,10,0):", $temp_0'$2_vec_map_VecMap'address_$0_market_ColData''} $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' == $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'';

    // trace_local[collaterals]($t0) at ./sources/market.move:166:54+1
    $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' := $Dereference($t0);
    assume {:print "$track_local(15,10,0):", $temp_0'$2_vec_map_VecMap'address_$0_market_ColData''} $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'' == $temp_0'$2_vec_map_VecMap'address_$0_market_ColData'';

    // goto L5 at ./sources/market.move:166:54+1
    goto L5;

    // label L4 at <internal>:1:1+10
    assume {:print "$at(1,0,10)"} true;
L4:

    // destroy($t0) at <internal>:1:1+10

    // goto L3 at <internal>:1:1+10
    goto L3;

    // label L5 at ./sources/market.move:167:5+1
    assume {:print "$at(20,6443,6444)"} true;
L5:

    // return () at ./sources/market.move:167:5+1
    $ret0 := $t0;
    return;

    // label L6 at ./sources/market.move:167:5+1
L6:

    // abort($t8) at ./sources/market.move:167:5+1
    $abort_code := $t8;
    $abort_flag := true;
    return;

}
