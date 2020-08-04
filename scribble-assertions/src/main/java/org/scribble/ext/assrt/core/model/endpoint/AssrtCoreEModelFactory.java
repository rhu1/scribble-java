package org.scribble.ext.assrt.core.model.endpoint;

import java.util.List;

import org.scribble.core.type.name.MsgId;
import org.scribble.core.type.name.Role;
import org.scribble.core.type.session.Payload;
import org.scribble.ext.assrt.core.model.endpoint.action.AssrtCoreEAcc;
import org.scribble.ext.assrt.core.model.endpoint.action.AssrtCoreERecv;
import org.scribble.ext.assrt.core.model.endpoint.action.AssrtCoreEReq;
import org.scribble.ext.assrt.core.model.endpoint.action.AssrtCoreESend;
import org.scribble.ext.assrt.core.model.global.AssrtCoreEMsg;
import org.scribble.ext.assrt.core.type.formula.AssrtAFormula;
import org.scribble.ext.assrt.core.type.formula.AssrtBFormula;
import org.scribble.ext.assrt.core.type.name.AssrtAnnotDataName;
import org.scribble.ext.assrt.model.endpoint.AssrtEModelFactory;

public interface AssrtCoreEModelFactory extends AssrtEModelFactory
{

	AssrtCoreESend AssrtCoreESend(Role peer, MsgId<?> mid, Payload pay,
			AssrtBFormula ass, List<AssrtAFormula> sexprs,
			//LinkedHashMap<AssrtIntVar, AssrtAFormula> phantoms,
			List<AssrtAnnotDataName> phantoms,
			AssrtBFormula phantAss);
	AssrtCoreERecv AssrtCoreERecv(Role peer, MsgId<?> mid, Payload pay,
			AssrtBFormula ass, List<AssrtAFormula> sexprs,
			//LinkedHashMap<AssrtIntVar, AssrtAFormula> phantoms,
			List<AssrtAnnotDataName> phantoms,
			AssrtBFormula phantAss);
	AssrtCoreEReq AssrtCoreEReq(Role peer, MsgId<?> mid, Payload pay,
			AssrtBFormula ass, List<AssrtAFormula> sexprs);
	AssrtCoreEAcc AssrtCoreEAcc(Role peer, MsgId<?> mid, Payload pay,
			AssrtBFormula ass, List<AssrtAFormula> sexprs);
	
	AssrtCoreEMsg AssrtCoreEMsg(Role peer, MsgId<?> mid, Payload pay,
			AssrtBFormula ass);// List<AssrtAFormula> sexprs);
			//Map<AssrtIntVarFormula, AssrtIntVarFormula> shadow);
}
