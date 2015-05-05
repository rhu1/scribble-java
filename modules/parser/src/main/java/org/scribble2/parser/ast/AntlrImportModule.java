package org.scribble2.parser.ast;

import org.antlr.runtime.tree.CommonTree;
import org.scribble2.model.ImportModule;
import org.scribble2.model.ModelFactoryImpl;
import org.scribble2.model.name.KindedNameNode;
import org.scribble2.model.name.SimpleKindedNameNode;
import org.scribble2.parser.ScribbleParser;
import org.scribble2.parser.ast.name.AntlrQualifiedName;
import org.scribble2.parser.ast.name.AntlrSimpleName;
import org.scribble2.sesstype.kind.ModuleKind;

public class AntlrImportModule
{
	public static final int MODULENAME_CHILD_INDEX = 0;
	public static final int ALIAS_CHILD_INDEX = 1; 

	private static final String EMPTY_ALIAS = "EMPTY_ALIAS";

	public static ImportModule parseImportModule(ScribbleParser parser, CommonTree ct)
	{
		/*ModuleNameNode fmn = AntlrQualifiedName.toModuleNameNode(getModuleNameChild(ct));
		SimpleProtocolNameNode alias = null;*/
		KindedNameNode<ModuleKind> fmn = AntlrQualifiedName.toModuleNameNode(getModuleNameChild(ct));
		SimpleKindedNameNode<ModuleKind> alias = null;
		if (hasAlias(ct))
		{
			//alias = AntlrSimpleName.toSimpleProtocolNameNode(getAliasChild(ct));
			alias = AntlrSimpleName.toSimpleModuleNameNode(getAliasChild(ct));  // FIXME: hardcoded to global
		}
		//return new ImportModule(fmn, alias);
		return ModelFactoryImpl.FACTORY.ImportModule(fmn, alias);
	}

	public static CommonTree getModuleNameChild(CommonTree ct)
	{
		return (CommonTree) ct.getChild(MODULENAME_CHILD_INDEX);
	}

	public static CommonTree getAliasChild(CommonTree ct)
	{
		return (CommonTree) ct.getChild(ALIAS_CHILD_INDEX);
	}
	
	public static boolean hasAlias(CommonTree ct)
	{
		//return ct.getChildCount() > 1;
		return !ct.getChild(ALIAS_CHILD_INDEX).getText().equals(EMPTY_ALIAS);
	}
}
