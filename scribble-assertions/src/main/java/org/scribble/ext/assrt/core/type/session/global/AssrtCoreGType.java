package org.scribble.ext.assrt.core.type.session.global;

import java.util.List;

import org.scribble.core.type.kind.Global;
import org.scribble.core.type.name.Role;
import org.scribble.ext.assrt.core.job.AssrtCore;
import org.scribble.ext.assrt.core.type.formula.AssrtBFormula;
import org.scribble.ext.assrt.core.type.name.AssrtAnnotDataName;
import org.scribble.ext.assrt.core.type.session.AssrtCoreSType;
import org.scribble.ext.assrt.core.type.session.AssrtCoreSTypeFactory;
import org.scribble.ext.assrt.core.type.session.AssrtCoreSyntaxException;
import org.scribble.ext.assrt.core.type.session.local.AssrtCoreLType;
import org.scribble.ext.assrt.core.visit.global.AssrtCoreGTypeInliner;


public interface AssrtCoreGType extends AssrtCoreSType<Global, AssrtCoreGType>
{
	
	// CHECKME: refactor as visitors?
	
	AssrtCoreGType inline(AssrtCoreGTypeInliner v);
	AssrtCoreGType pruneRecs(AssrtCore core);

	AssrtCoreLType projectInlined(AssrtCoreSTypeFactory af, Role self,
			AssrtBFormula f) throws AssrtCoreSyntaxException;  // N.B. checking "mergability"
	
	List<AssrtAnnotDataName> collectAnnotDataVarDecls();  // Currently only the vars are needed (not the data types)
}

