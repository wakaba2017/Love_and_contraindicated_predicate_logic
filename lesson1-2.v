Theorem ch1_2 :
forall P Q R S T U V Y Z : Prop,
  (Y -> Z) ->
  P ->
  Q ->
  R ->
  S ->
  T ->
  ((T /\ Q /\ R) -> U) ->
  ((U /\ S) -> V) ->
  ((P /\ V) -> Y) ->
  Z.
(*

前提

  P:蜜川さんは庭で採れた木の実をスターアニスと言って馬場園さんに渡した。
  Q:日本にスターアニスは自生していない。
  R:蜜川さんは関西育ちで日本を出たことがない。
  S:蜜川さんの母親はスターアニスをよく料理に使っていた。
  T:蜜川さんはスターアニスを「子供のころ外に採りに行かされた」と言った。
  U:蜜川さんがスターアニスと呼んだのは本当はしきみの実である。
  V:蜜川さんはしきみの実のことを知っていた。
  Y:相手が死ぬ可能性を認識していたにもかかわらず、あえてその行為をした。
  Z:行為は故意である。

  Y -> Z:
    相手が死ぬ可能性を認識していたにもかかわらず、あえてその行為をした　ならば
    行為は故意である。

  (T /\ Q /\ R) -> U:
    (蜜川さんはスターアニスを「子供のころ外に採りに行かされた」と言った　かつ
     蜜川さんは関西育ちで日本を出たことがない　かつ
     日本にスターアニスは自生していない)  ならば
    蜜川さんがスターアニスと呼んだのは本当はしきみの実である。

  (U /\ S) -> V
    (蜜川さんがスターアニスと呼んだのは本当はしきみの実である　かつ
     蜜川さんの母親はスターアニスをよく料理に使っていた)  ならば
    蜜川さんはしきみの実のことを知っていた。

  (P /\ V) -> Y:
    (蜜川さんは庭で採れた木の実をスターアニスと言って馬場園さんに渡した　かつ
     蜜川さんはしきみの実のことを知っていた)  ならば
    相手が死ぬ可能性を認識していたにもかかわらず、あえてその行為をした。

結論

  Z:行為は故意である。

*)
Proof.
  intros P Q R S T U V Y Z A1 A2 A3 A4 A5 A6 A7 A8 A9.
  apply A1.
  apply A9.
  split.
  - (* Pが成立することの証明 *)
    apply A2.
  - (* Vが成立することの証明 *)
    apply A8.
    split.
    + (* Uが成立することの証明 *)
      apply A7.
      split.
      * (* Tが成立することの証明 *)
        apply A6.
      * (* Q/\Rが成立することの証明 *)
        split.
        { (* Qが成立することの証明 *)
          apply A3.
        }
        { (* Rが成立することの証明 *)
          apply A4.
        }
    + (* Sが成立することの証明 *)
      apply A5.
Qed.

From mathcomp
Require Import ssreflect.

Theorem ch1_2_ssr :
forall P Q R S T U V Y Z : Prop,
  (Y -> Z) ->
  P ->
  Q ->
  R ->
  S ->
  T ->
  ((T /\ Q /\ R) -> U) ->
  ((U /\ S) -> V) ->
  ((P /\ V) -> Y) ->
  Z.
Proof.
  intros P Q R S T U V Y Z A1 A2 A3 A4 A5 A6 A7 A8 A9.
  apply: A1.
  apply: A9.
  split.
  - (* Pが成立することの証明 *)
    apply: A2.
  - (* Vが成立することの証明 *)
    apply: A8.
    split.
    + (* Uが成立することの証明 *)
      apply: A7.
      split.
      * (* Tが成立することの証明 *)
        apply: A6.
      * (* Q/\Rが成立することの証明 *)
        split.
        { (* Qが成立することの証明 *)
          apply: A3.
        }
        { (* Rが成立することの証明 *)
          apply: A4.
        }
    + (* Sが成立することの証明 *)
      apply: A5.
Qed.
