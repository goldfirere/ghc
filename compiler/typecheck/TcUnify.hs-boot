module TcUnify where
import TcType     ( TcTauType )
import TcRnTypes  ( TcM )
import TcEvidence ( TcCoercion )
import Coercion   ( Coercion )

unifyType   :: TcTauType -> TcTauType -> TcM TcCoercion
unifyTypeCo :: TcTauType -> TcTauType -> TcM Coercion
