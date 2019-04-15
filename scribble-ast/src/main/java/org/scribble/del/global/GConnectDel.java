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
package org.scribble.del.global;

import java.util.List;

import org.scribble.ast.ScribNode;
import org.scribble.ast.global.GConnect;
import org.scribble.ast.name.simple.RoleNode;
import org.scribble.core.type.name.Role;
import org.scribble.core.type.session.Msg;
import org.scribble.del.ConnectionActionDel;
import org.scribble.util.ScribException;
import org.scribble.visit.GTypeTranslator;
import org.scribble.visit.NameDisambiguator;

public class GConnectDel extends ConnectionActionDel
		implements GSimpleSessionNodeDel
{
	public GConnectDel()
	{
		
	}

	@Override
	public ScribNode leaveDisambiguation(ScribNode child,
			NameDisambiguator disamb, ScribNode visited) throws ScribException
	{
		GConnect gc = (GConnect) visited;
		return gc;
	}
	
	@Override
	public org.scribble.core.type.session.global.GConnect translate(ScribNode n,
			GTypeTranslator t) throws ScribException
	{
		GConnect source = (GConnect) n;
		Role src = source.getSourceChild().toName();
		List<RoleNode> ds = source.getDestinationChildren();
		if (ds.size() > 1)
		{
			throw new RuntimeException("TODO: multiple destination roles: " + source);
		}
		Role dst = ds.get(0).toName();
		Msg msg = source.getMessageNodeChild().toMsg();
		return new org.scribble.core.type.session.global.GConnect(source, src, msg, dst);
	}
}
