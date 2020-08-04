package org.scribble.ext.assrt.core.model.global.action;

import java.util.List;
import java.util.stream.Collectors;

import org.scribble.ext.assrt.core.type.formula.AssrtAFormula;
import org.scribble.ext.assrt.core.type.formula.AssrtBFormula;

public interface AssrtCoreSAction
{
	AssrtBFormula getAssertion();

	default String assertionToString()
	{
		AssrtBFormula ass = getAssertion();
		return "{" + ass.toString() + "}";
	}

	List<AssrtAFormula> getStateExprs();  // Cf. AssrtCoreEAction
	
	default String stateExprsToString()
	{
		List<AssrtAFormula> exprs = getStateExprs();
		return //(exprs.isEmpty() ? "" :
			"<" + exprs.stream().map(Object::toString)
						.collect(Collectors.joining(", ")) + ">";
	}
}
