package org.scribble.model.local;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.StringReader;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.scribble.sesstype.Payload;
import org.scribble.sesstype.name.DataType;
import org.scribble.sesstype.name.MessageId;
import org.scribble.sesstype.name.MessageSigName;
import org.scribble.sesstype.name.Op;
import org.scribble.sesstype.name.Role;

public class AutParser
{
	public AutParser()
	{

	}
	
	public EndpointGraph parse(String aut)
	{
		//Map<Integer, Map<String, Integer>> edges = new HashMap<>();
		Map<Integer, List<String>> as = new HashMap<>();
		Map<Integer, List<Integer>> succs = new HashMap<>();
		int init = -1;
		try
		{
			BufferedReader br = new BufferedReader(new StringReader(aut));
			String line = br.readLine();
			if (line == null || !line.startsWith("des (") || !line.endsWith(")"))
			{
				throw new RuntimeException("Unexpected first line: " + line);
			}
			String[] first = line.substring("des (".length(), line.length() - 1).split(",");
			if (first.length != 3)
			{
				throw new RuntimeException("Unexpected first line: " + line);
			}
			init = Integer.parseInt(first[0]);
			//int trans = Integer.parseInt(first[1]);
			//int states = Integer.parseInt(first[2]);
			while ((line = br.readLine()) != null)
			{
				if (!line.startsWith("(") || !line.endsWith(")"))
				{
					throw new RuntimeException("Unexpected line: " + line);
				}
				String[] read = line.substring(1, line.length()-1).split(",");
				int s = Integer.parseInt(read[0]);
				String a = read[1].substring(1, read[1].length()-1);
				int succ = Integer.parseInt(read[2]);
				//Map<String, Integer> tmp = edges.get(s);
				List<String> tmp1 = as.get(s);
				List<Integer> tmp2 = succs.get(s);
				if (tmp1 == null)
				{
					//tmp = new HashMap<>();
					//edges.put(s, tmp);
					tmp1 = new LinkedList<>();
					as.put(s, tmp1);
					tmp2 = new LinkedList<>();
					succs.put(s, tmp2);
				}
				//tmp.put(a, succ);
				tmp1.add(a);
				tmp2.add(succ);
			}
		}
		catch (IOException e)
		{
			throw new RuntimeException(e);
		}
		//Set<Integer> allSuccs = edges.values().stream().flatMap((j) -> j.values().stream()).collect(Collectors.toSet());
		Set<Integer> allSuccs = succs.values().stream().flatMap((j) -> j.stream()).collect(Collectors.toSet());
		int term = -1;
		//Set<Integer> terms = allSuccs.stream().filter((j) -> !edges.containsKey(j)).collect(Collectors.toSet());
		Set<Integer> terms = allSuccs.stream().filter((j) -> !succs.containsKey(j)).collect(Collectors.toSet());
		if (terms.size() > 0)
		{
			term = terms.iterator().next();
		}
		LGraphBuilder builder = new LGraphBuilder();
		builder.reset();
		Map<Integer, EndpointState> map = new HashMap<>();
		map.put(init, builder.getEntry());
		if (term != -1)
		{
			map.put(term, builder.getExit());
		}
		map.put(init, builder.getEntry());
		//for (int i : edges.keySet())
		for (int i : as.keySet())
		{
			if (i != init && i != term)
			{
				map.put(i, builder.newState(Collections.emptySet()));
			}
		}
		//for (int i : succs)
		for (int i : succs.keySet())
		{
			if (!map.containsKey(i) && i != init && i != term)
			{
				map.put(i, builder.newState(Collections.emptySet()));
			}
		}
		//for (int i : edges.keySet())
		for (int i : as.keySet())
		{
			EndpointState s = map.get(i);
			//Map<String, Integer> tmp = edges.get(i);
			List<String> tmp1 = as.get(i);
			List<Integer> tmp2 = succs.get(i);
			//if (tmp != null)
			if (tmp1 != null)
			{
				//for (String a : tmp.keySet())
				Iterator<Integer> is = tmp2.iterator();
				for (String a : tmp1)
				{
					int succ = is.next();
					//builder.addEdge(s, parseIOAction(a), map.get(tmp.get(a)));
					builder.addEdge(s, parseIOAction(a), map.get(succ));
				}
			}
		}
		//return builder.finalise();
		return new EndpointGraph(builder.getEntry(), builder.getExit());
	}
	
	private static IOAction parseIOAction(String a)
	{
		String peer;
		String action;
		String msg;  // Could be an Op or a MessageSigName (affects API generation)
		String[] pay = null;
		
		int i = a.indexOf("!");
		i = (i == -1) ? a.indexOf("?") : i;
		int j = i+1;
		String tmp = a.substring(j, j+1);
		if (tmp.equals("!") || tmp.equals("?"))
		{
			j++;
		}
		action = a.substring(i, j);
	
		peer = a.substring(0, i);
		int k = a.indexOf("(");
		msg = a.substring(j, k);
		String p = a.substring(k+1, a.length()-1);
		if (!p.isEmpty())
		{
			pay = p.split(",");
		}
		switch (action)
		{
			case "!":
			{
				Payload payload = (pay != null) ? new Payload(Arrays.asList(pay).stream().map((pe) -> new DataType(pe)).collect(Collectors.toList())) : Payload.EMPTY_PAYLOAD;
				return new Send(new Role(peer), getMessageIdHack(msg), payload);  // FIXME: how about MessageSiGnames? -- currently OK, treated as empty payload (cf. ModelAction)
			}
			case "?":
			{
				Payload payload = (pay != null) ? new Payload(Arrays.asList(pay).stream().map((pe) -> new DataType(pe)).collect(Collectors.toList())) : Payload.EMPTY_PAYLOAD;
				return new Receive(new Role(peer), getMessageIdHack(msg), payload);  // FIXME: how about messagesignames?)
			}
			case "!!":
			{
				return new Connect(new Role(peer));
			}
			case "??":
			{
				return new Accept(new Role(peer));
			}
			default:
			{
				throw new RuntimeException("Shouldn't get in here: " + msg);
			}
		}
	}
	
	// Cf. ModelState.toAut, ModelAction.toStringWithMessageIdHack
	private static MessageId<?> getMessageIdHack(String msg)
	{
		return (msg.startsWith("^")) ? new MessageSigName(msg.substring(1)) : new Op(msg);
	}
}
