package org.scribble.ext.assrt.main;

import java.nio.file.Path;
import java.util.Map;

import org.scribble.ast.AstFactory;
import org.scribble.ast.Module;
import org.scribble.core.job.CoreArgs;
import org.scribble.core.type.name.ModuleName;
import org.scribble.del.DelFactory;
import org.scribble.ext.assrt.ast.AssrtAstFactoryImpl;
import org.scribble.ext.assrt.parser.scribble.AssrtScribbleAntlrWrapper;
import org.scribble.main.Main;
import org.scribble.main.resource.locator.ResourceLocator;
import org.scribble.parser.ScribAntlrWrapper;
import org.scribble.util.ScribException;
import org.scribble.util.ScribParserException;

public class AssrtMain extends Main
{
	//public final Solver solver; //= Solver.NATIVE_Z3;
	//public final boolean batching;

	// Load main module from file system
	public AssrtMain(ResourceLocator locator, Path mainpath,
			Map<CoreArgs, Boolean> args) throws ScribException, ScribParserException
	{
		super(locator, mainpath, args);
	}

	@Override
	protected ScribAntlrWrapper newAntlr()
	{
		return new AssrtScribbleAntlrWrapper();
	}
	
	@Override
	protected AstFactory newAstFactory(ScribAntlrWrapper antlr)
	{
		return new AssrtAstFactoryImpl();
	}

	@Override
	public AssrtJob newJob(Map<ModuleName, Module> parsed,
			Map<CoreArgs, Boolean> args, ModuleName mainFullname, AstFactory af,
			DelFactory df)
	{
		return new AssrtJob(parsed, args, mainFullname, af, df);
	}
}