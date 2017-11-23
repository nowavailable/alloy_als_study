module main
enum State { before, after }

// Boundaryは、何らかの1次元の位置、つまり何らかの値を表す。
sig Boundary { val: one Int }  
sig Participant {
  loto_num: one Boundary,
  prize_num: lone Boundary,
  // 状態変化を表現することを目的に付加したフィールド
  meta_identifier: one Int,
  meta_state: one State
}
fact {
  /** meta_state は、beforeかafterしかない。つまり、事前と事後。*/
  all p:Participant | p.meta_state = before or p.meta_state = after
  /** 
   ID が等しいふたつAtomがあったら、
   それはひとつのAtomの事前状態と事後状態であると考える。
  */
  all p,p':Participant |
    (p != p' and p.meta_identifier = p'.meta_identifier) => 
      (p.meta_state != p'.meta_state)
}

--------------------------------------------------------------
-- くじ引きとしてloto_numがあり、
-- loto_num の値が一番大きかったParticipantに、
-- prize_num、つまり賞品が与えられている。 
--------------------------------------------------------------
-- 事前条件
pred BeforeLoto {
  all participant:Participant |
    participant.meta_state = before => 
      /** 誰も賞品を与えられていないこと。*/
      participant.prize_num = none
}
-- 不変条件
pred Immutable {
  all participant:Participant |
    /** 事前状態、事後状態それぞれの中で、IDとloto_numは重複していないこと。 */
    participant.meta_state = before => 
      all p,p':participant |
        p != p' => eternalUnique[p,p']
    &&
    participant.meta_state = after => 
      all p,p':participant |
        p != p' => eternalUnique[p,p']
  /** 
   IDが等しく、状態が異なるAto同士は、loto_numが共通であること。
   それ以外は、loto_numは必ず異なる。
  */
  all p,p':Participant |
    p != p' implies (
      (p.meta_identifier = p'.meta_identifier and
      p.meta_state != p'.meta_state) implies 
        (p.loto_num = p'.loto_num) && (p.loto_num.val = p'.loto_num.val) else
          (p.loto_num != p'.loto_num) && (p.loto_num.val != p'.loto_num.val)
    )
}
pred eternalUnique[p:Participant,p':Participant] {
  (p.meta_identifier != p'.meta_identifier) and (p.loto_num != p'.loto_num)
}

/** 
 状態変化のための条件：loto_numがmaxであること。
 そのmaxであるloto_numを返す。
*/
fun win_num : Int{
  Boundary.(Participant.(Participant<:loto_num)<:val).max
}
-- 事後条件
pred AfterLoto {
  /** 事後状態Atomには必ず、対になる事前状態のAtomが存在すること。*/
  Participant.(
    (Participant<:meta_state & Participant->after).State<:meta_identifier
  )  // 抽選後参加者 とそのID、から、IDだけを取り出す
  in
  Participant.(
    (Participant<:meta_state & Participant->before).State<:meta_identifier
  )  // 抽選前参加者 とそのID、から、IDだけを取り出す
  && 
  /** loto_num がmaxの者だけが prize_num を持っていること。*/
  let winner = loto_num:>(Boundary<:val & Boundary->win_num).Int |
    Participant<:prize_num in winner
}

run {Immutable && BeforeLoto && AfterLoto} 
  for 3 but 4 Participant, 3 Int
