/**
 * Copyright 2008 The Scribble Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software distributed under the License
 * is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
 * or implied. See the License for the specific language governing permissions and limitations under
 * the License.
 */
package org.scribble.visit.context;

import org.scribble.ast.ScribNode;
import org.scribble.core.lang.context.ModuleContext;
import org.scribble.lang.Lang;
import org.scribble.lang.context.ModuleContextMaker;
import org.scribble.util.ScribException;
import org.scribble.visit.AstVisitor;

// Disambiguates ambiguous PayloadTypeOrParameter names and inserts implicit Scope names
public class ModuleContextBuilder extends AstVisitor
{
	public final ModuleContextMaker maker = new ModuleContextMaker();  // TODO: HACK, refactor

	private ModuleContext mcontext;  // The "root" Module context (not the "main" module)
	
	public ModuleContextBuilder(Lang job)
	{
		super(job);
	}

	@Override
	protected void enter(ScribNode parent, ScribNode child)
			throws ScribException
	{
		//System.out.println("mmm1: " + child.getClass() + " ,, " + child.del());
		child.del().enterModuleContextBuilding(parent, child, this);
	}

	@Override
	protected ScribNode leave(ScribNode parent, ScribNode child,
			ScribNode visited) throws ScribException
	{
		return visited.del().leaveModuleContextBuilding(parent, child, this,
				visited);
	}
	
	public void setModuleContext(ModuleContext mcontext)
	{
		this.mcontext = mcontext;
	}
	
	public ModuleContext getModuleContext()
	{
		return this.mcontext;
	}
}
