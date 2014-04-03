module LOTOS where

import LOTOS.AST
import LOTOS.Parser
import LOTOS.Simplify
import LOTOS.Synthesize

import Data.List
import Unbound.LocallyNameless hiding (union)
import Unbound.LocallyNameless.Ops

simpleParse :: String -> Process
simpleParse s = case parseProcess "" s of
    Left err -> error $ show err
    Right p -> p

pair :: Name Process -> Bool -> Process -> Process -> Process
pair name sync p1@(Process name1 (Embed binding1)) p2@(Process name2 (Embed binding2)) = Process name $ Embed $ bind formals $ bind (rec [p1, p2]) b
    where
    -- Use unsafeUnbind so we can cheat by having formal gate params mean the same thing in different ASTs.
    ((formalGates1, formalParams1), _) = unsafeUnbind binding1
    ((formalGates2, formalParams2), _) = unsafeUnbind binding2
    b1 = Instantiate name1 formalGates1 $ map Variable formalParams1
    b2 = Instantiate name2 formalGates2 $ map Variable formalParams2
    formalGates = formalGates1 `union` formalGates2
    (gates, b) = if sync then ([], Hide $ bind formalGates $ Parallel formalGates b1 b2) else (formalGates, Interleaving b1 b2)
    formals = (gates, formalParams1 ++ formalParams2)

uncontrolled_gates :: [Gate]
uncontrolled_gates = map s2n ["os.req", "dev.sent", "dev.receive"]

os_send_spec, dev_send_spec, os_recv_spec, dev_recv_spec, os_spec, dev_spec :: Process
os_send_spec = simpleParse "process os_send[class.send, class.sent, class.notsent] := os.req ?msg; class.send !msg; (class.sent; os.complete; exit [] class.notsent ?err; os.failed !err; exit) endproc"
dev_send_spec = simpleParse "process dev_send[class.send, class.sent, class.notsent] := dev.enqueue ?packet; class.send !packet; dev.sent ?status; (class.sent; exit [] class.notsent !status; exit) endproc"
os_recv_spec = simpleParse "process os_recv[class.receive] := class.receive ?packet; os.arrive !packet; exit endproc"
dev_recv_spec = simpleParse "process dev_recv[class.receive] := dev.receive ?packet; class.receive !packet; exit endproc"
os_spec = pair (s2n "os_spec") False os_send_spec os_recv_spec
dev_spec = pair (s2n "dev_spec") False dev_send_spec dev_recv_spec

make_sample :: String -> Process -> Process -> Process
make_sample name p1 p2 = simplifyProcess $ pair (s2n name) True p1 p2

send_sample, recv_sample, full_sample :: Process
send_sample = make_sample "send" os_send_spec dev_send_spec
recv_sample = make_sample "recv" os_recv_spec dev_recv_spec
full_sample = make_sample "full" os_spec dev_spec

join_sample :: Process
join_sample = simplifyProcess $ pair (s2n "join") False send_sample recv_sample

cg_send, cg_recv, cg_full, cg_join :: Program
cg_send = codegen uncontrolled_gates send_sample
cg_recv = codegen uncontrolled_gates recv_sample
cg_full = codegen uncontrolled_gates full_sample
cg_join = codegen uncontrolled_gates join_sample
