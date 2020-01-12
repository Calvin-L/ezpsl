---- MODULE Test ----

EXTENDS Integers, Sequences, TLC

\* #include Test.ezs
CONSTANTS _Undefined, main_calls
VARIABLES _pc, _frames, _actor, x
vars == <<_pc, _frames, _actor, x>>
symmetry == UNION {Permutations(main_calls)}
Init ==
  /\ _pc = [_pid \in main_calls |-> <<"_line_00006">>]
  /\ _frames = [_pid \in main_calls |-> << <<>> >>]
  /\ _actor = _Undefined
  /\ x = 0
_line_00006(_self) ==
  /\ (Len(_pc[_self]) > 0)
  /\ (_pc[_self][Len(_pc[_self])] = "_line_00006")
  /\ ((_actor = _Undefined) \/ (_actor = _self))
  /\ LET _tmp == _self IN
    /\ LET _tmp_1 == x IN
      /\ LET _tmp_2 == (SubSeq(_pc[_self], 1, (Len(_pc[_self]) - 1)) \o <<"_line_00007">>) IN
        /\ _actor' = _tmp
        /\ _pc' = [_pc EXCEPT ![_self] = _tmp_2]
        /\ _frames' = [_frames EXCEPT ![_self][Len(_frames[_self])] = ("tmp" :> _tmp_1) @@ @]
        /\ UNCHANGED x
_line_00007(_self) ==
  /\ (Len(_pc[_self]) > 0)
  /\ (_pc[_self][Len(_pc[_self])] = "_line_00007")
  /\ ((_actor = _Undefined) \/ (_actor = _self))
  /\ LET _tmp_3 == _self IN
    /\ LET _tmp_4 == _Undefined IN
      /\ LET _tmp_5 == (SubSeq(_pc[_self], 1, (Len(_pc[_self]) - 1)) \o <<"_line_00008">>) IN
        /\ _actor' = _tmp_4
        /\ _pc' = [_pc EXCEPT ![_self] = _tmp_5]
        /\ _frames' = [_frames EXCEPT ![_self][Len(_frames[_self])] = ("tmp" :> (LET _myframes == _frames[_self] IN _myframes[Len(_myframes)].tmp)) @@ @]
        /\ UNCHANGED x
_line_00008(_self) ==
  /\ (Len(_pc[_self]) > 0)
  /\ (_pc[_self][Len(_pc[_self])] = "_line_00008")
  /\ ((_actor = _Undefined) \/ (_actor = _self))
  /\ LET _tmp_6 == _self IN
    /\ LET _tmp_7 == ((LET _myframes == _frames[_self] IN _myframes[Len(_myframes)].tmp) + 1) IN
      /\ LET _tmp_8 == (SubSeq(_pc[_self], 1, (Len(_pc[_self]) - 1)) \o <<"_line_00009">>) IN
        /\ _actor' = _tmp_6
        /\ x' = _tmp_7
        /\ _pc' = [_pc EXCEPT ![_self] = _tmp_8]
        /\ _frames' = [_frames EXCEPT ![_self][Len(_frames[_self])] = ("tmp" :> (LET _myframes == _frames[_self] IN _myframes[Len(_myframes)].tmp)) @@ @]
_line_00009(_self) ==
  /\ (Len(_pc[_self]) > 0)
  /\ (_pc[_self][Len(_pc[_self])] = "_line_00009")
  /\ ((_actor = _Undefined) \/ (_actor = _self))
  /\ LET _tmp_9 == _self IN
    /\ LET _tmp_10 == SubSeq(_pc[_self], 1, (Len(_pc[_self]) - 1)) IN
      /\ _actor' = _tmp_9
      /\ _pc' = [_pc EXCEPT ![_self] = _tmp_10]
      /\ _frames' = [_frames EXCEPT ![_self][Len(_frames[_self])] = ("tmp" :> (LET _myframes == _frames[_self] IN _myframes[Len(_myframes)].tmp)) @@ @]
      /\ UNCHANGED x
_halt(_self) ==
  /\ _pc[_self] = <<>>
  /\ _actor = _self
  /\ _actor' = _Undefined
  /\ UNCHANGED _frames
  /\ UNCHANGED _pc
  /\ UNCHANGED x
Next ==
  \E _pid \in UNION {main_calls}:
    \/ _line_00006(_pid)
    \/ _line_00007(_pid)
    \/ _line_00008(_pid)
    \/ _line_00009(_pid)
    \/ _halt(_pid)
\* /include Test.ezs

Invariant ==
  /\ (_actor = _Undefined) => (x <= 2)
  /\ (\A c \in main_calls: _pc[c] = <<>>) => (x = 2)

=====================
