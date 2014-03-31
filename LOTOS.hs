module LOTOS where

import LOTOS.AST
import LOTOS.Parser
import LOTOS.Simplify
import LOTOS.Synthesize

import Unbound.LocallyNameless

simpleParse :: String -> Behavior
simpleParse s = case parseBehavior "" s of
    Left err -> error $ show err
    Right b -> b

uncontrolled_gates, class_gates :: [Gate]
uncontrolled_gates = map s2n ["os.req", "dev.sent", "dev.receive"]
class_gates = map s2n ["class.send", "class.sent", "class.notsent", "class.receive"]

os_send_spec, dev_send_spec, os_recv_spec, dev_recv_spec, os_spec, dev_spec :: Behavior
os_send_spec = simpleParse "os.req ?msg; class.send !msg; (class.sent; os.complete; exit [] class.notsent ?err; os.failed !err; exit)"
dev_send_spec = simpleParse "dev.enqueue ?packet; class.send !packet; dev.sent ?status; (class.sent; exit [] class.notsent !status; exit)"
os_recv_spec = simpleParse "class.receive ?packet; os.arrive !packet; exit"
dev_recv_spec = simpleParse "dev.receive ?packet; class.receive !packet; exit"
os_spec = Interleaving os_send_spec os_recv_spec
dev_spec = Interleaving dev_send_spec dev_recv_spec

make_sample :: [Gate] -> Behavior -> Behavior -> Behavior
make_sample classes b1 b2 = simplify $ Hide $ bind classes $ Parallel classes b1 b2

send_sample, recv_sample, full_sample :: Behavior
send_sample = make_sample class_gates os_send_spec dev_send_spec
recv_sample = make_sample class_gates os_recv_spec dev_recv_spec
full_sample = make_sample class_gates os_spec dev_spec

cg_send, cg_recv, cg_full :: Program
cg_send = codegen uncontrolled_gates send_sample
cg_recv = codegen uncontrolled_gates recv_sample
cg_full = codegen uncontrolled_gates full_sample
