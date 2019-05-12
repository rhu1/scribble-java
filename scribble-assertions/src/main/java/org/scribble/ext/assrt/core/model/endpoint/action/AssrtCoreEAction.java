package org.scribble.ext.assrt.core.model.endpoint.action;

import java.util.List;
import java.util.stream.Collectors;

import org.scribble.ext.assrt.core.type.formula.AssrtArithFormula;
import org.scribble.ext.assrt.model.endpoint.action.AssrtEAction;

public interface AssrtCoreEAction extends AssrtEAction
{
	//AssrtDataTypeVar DUMMY_VAR = new AssrtDataTypeVar("_dum0");  // for statevars -- cf. actionvars, AssrtCoreGProtocolTranslator::makeFreshDataTypeVar starts from 1

	/*AssrtDataTypeVar getAnnotVar();
	AssrtArithFormula getArithExpr();*/
	List<AssrtArithFormula> getStateExprs();  // Cf. AssrtStateVarArgAnnotNode::getAnnotExprs
	
	default String stateExprsToString()
	{
		List<AssrtArithFormula> exprs = getStateExprs();
		return exprs.isEmpty() 
				? "" 
				: ("<" + exprs.stream().map(Object::toString)
						.collect(Collectors.joining(", ")) + ">");
	}
}
