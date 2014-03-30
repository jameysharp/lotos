module LOTOS where

import LOTOS.AST
import LOTOS.Controllable
import LOTOS.Parser
import LOTOS.Simplify

import Unbound.LocallyNameless

sample :: Behavior
sample = simplify $ uncontrolled [s2n "os.req", s2n "dev.irq"] $ simplify $ Hide $ bind class_gates $ Parallel class_gates os_spec dev_spec

class_gates :: [Gate]
class_gates = [s2n "class.send", s2n "class.ok", s2n "class.err"]

os_spec, dev_spec :: Behavior
Right os_spec = parseBehavior "" "os.req ?msg; class.send !msg; (class.ok; os.complete; exit [] class.err ?err; os.failed !err; exit)"
Right dev_spec = parseBehavior "" "dev.enqueue ?packet; class.send !packet; dev.irq ?status; (class.ok; exit [] class.err !status; exit)"
