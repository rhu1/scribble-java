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
package org.scribble.type.session;

import java.util.Collections;
import java.util.List;
import java.util.Set;

import org.antlr.runtime.tree.CommonTree;
import org.scribble.type.kind.ProtocolKind;
import org.scribble.type.name.ProtocolName;
import org.scribble.type.name.RecVar;
import org.scribble.visit.STypeInliner;
import org.scribble.visit.STypeUnfolder;

public abstract class BasicInteraction<K extends ProtocolKind>
		extends STypeBase<K> implements SType<K>
{
	public BasicInteraction(CommonTree source)
	{
		super(source);
	}

	@Override
	public Set<RecVar> getRecVars()
	{
		return Collections.emptySet();
	}
	
	@Override
	public BasicInteraction<K> pruneRecs()
	{
		return this;
	}

	@Override
	public BasicInteraction<K> getInlined(STypeInliner v)
	{
		return this;
	}

	@Override
	public BasicInteraction<K> unfoldAllOnce(STypeUnfolder<K> u)
	{
		return this;
	}

	@Override
	public List<ProtocolName<K>> getProtoDependencies()
	{
		return Collections.emptyList();
	}
	
	@Override
	public CommonTree getSource()
	{
		return (CommonTree) super.getSource();
	}
}
