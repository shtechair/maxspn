package maxspn

import (
	"context"
	"log"
	"math"
	"time"
)

var ( // Main API
	_ = ExactMC
	_ = ExactFC
	_ = ExactFCnO
	_ = ExactFCnOnS
)

// Exact solver with Marginal Checking
func ExactMC(spn SPN, baseline float64, timeout int) float64 {
	ctx, _ := context.WithTimeout(context.Background(), time.Duration(timeout)*time.Second)
	x := make([]int, len(spn.Schema))
	return dfsMC(ctx, spn, x, 0, baseline)
}

func dfsMC(ctx context.Context, spn SPN, x []int, xi int, baseline float64) float64 {
	select {
	case <-ctx.Done():
		return baseline
	default:
	}

	if xi == len(spn.Schema) {
		return math.Max(baseline, evalUncompletedX(spn, x, xi))
	}
	x[xi] = 0
	if evalUncompletedX(spn, x, xi+1) > baseline {
		baseline = math.Max(baseline, dfsMC(ctx, spn, x, xi+1, baseline))
	}
	x[xi] = 1
	if evalUncompletedX(spn, x, xi+1) > baseline {
		baseline = math.Max(baseline, dfsMC(ctx, spn, x, xi+1, baseline))
	}
	return baseline
}

// Exact solver with Forwarding Checking
func ExactFC(spn SPN, baseline float64, timeout int) float64 {
	x := make([]int, len(spn.Schema))
	for i := range x {
		x[i] = -1
	}
	ctx, _ := context.WithTimeout(context.Background(), time.Duration(timeout)*time.Second)
	return dfsFC(ctx, spn, x, baseline)
}

func dfsFC(ctx context.Context, spn SPN, x []int, baseline float64) float64 {
	select {
	case <-ctx.Done():
		return baseline
	default:
	}

	x2 := make([]int, len(x))
	copy(x2, x)
	x = x2
	as := make([][]float64, len(x))
	for i := range as {
		as[i] = make([]float64, 2)
		if x[i] == 0 || x[i] == -1 {
			as[i][0] = 1
		}
		if x[i] == 1 || x[i] == -1 {
			as[i][1] = 1
		}
	}
	var d [][]float64
	for {
		updated := false
		d = derivativeOfAssignment(spn, as)
		for i := range x {
			if x[i] == -1 {
				xi0 := d[i][0]
				xi1 := d[i][1]

				if xi0 < baseline && xi1 < baseline {
					return baseline
				}
				if xi0 < baseline {
					x[i] = 1
					as[i][0] = 0
					updated = true
				}
				if xi1 < baseline {
					x[i] = 0
					as[i][1] = 0
					updated = true
				}
			}
		}
		if !updated {
			break
		}
	}
	maxVarID := -1
	maxValID := 0
	for i := range x {
		if x[i] == -1 {
			maxVarID = i
			break
		}
	}
	if i := maxVarID; i != -1 {
		x[i] = maxValID
		baseline = math.Max(dfsFC(ctx, spn, x, baseline), baseline)
		x[i] = maxValID ^ 1
		baseline = math.Max(dfsFC(ctx, spn, x, baseline), baseline)
		return baseline
	}
	return math.Max(baseline, math.Max(d[0][0], d[0][1]))
}

// Exact solver with Forward Checking + Ordering
func ExactFCnO(spn SPN, baseline float64, timeout int) float64 {
	x := make([]int, len(spn.Schema))
	for i := range x {
		x[i] = -1
	}
	ctx, _ := context.WithTimeout(context.Background(), time.Duration(timeout)*time.Second)
	return dfsFCnO(ctx, spn, x, baseline)
}

func dfsFCnO(ctx context.Context, spn SPN, x []int, baseline float64) float64 {
	select {
	case <-ctx.Done():
		return baseline
	default:
	}

	x2 := make([]int, len(x))
	copy(x2, x)
	x = x2
	as := make([][]float64, len(x))
	for i := range as {
		as[i] = make([]float64, 2)
		if x[i] == 0 || x[i] == -1 {
			as[i][0] = 1
		}
		if x[i] == 1 || x[i] == -1 {
			as[i][1] = 1
		}
	}
	var d [][]float64
	for {
		updated := false
		d = derivativeOfAssignment(spn, as)
		for i := range x {
			if x[i] == -1 {
				xi0 := d[i][0]
				xi1 := d[i][1]

				if xi0 < baseline && xi1 < baseline {
					return baseline
				}
				if xi0 < baseline {
					x[i] = 1
					as[i][0] = 0
					updated = true
				}
				if xi1 < baseline {
					x[i] = 0
					as[i][1] = 0
					updated = true
				}
			}
		}
		if !updated {
			break
		}
	}
	maxVarID := -1
	maxValID := -1
	maxDer := math.Inf(-1)
	for i := range x {
		if x[i] == -1 {
			crtValID := 0
			crtDer := d[i][0]
			if d[i][0] < d[i][1] {
				crtValID = 1
				crtDer = d[i][1]
			}
			if maxVarID == -1 || maxDer < crtDer {
				maxVarID = i
				maxValID = crtValID
				maxDer = crtDer
			}
		}
	}
	if i := maxVarID; i != -1 {
		x[i] = maxValID
		baseline = math.Max(dfsFCnO(ctx, spn, x, baseline), baseline)
		x[i] = maxValID ^ 1
		baseline = math.Max(dfsFCnO(ctx, spn, x, baseline), baseline)
		return baseline
	}
	return math.Max(baseline, math.Max(d[0][0], d[0][1]))
}

// Exact solver with Forward Checking + Ordering + Stage
func ExactFCnOnS(spn SPN, baseline float64, timeout int) float64 {
	ctx, _ := context.WithTimeout(context.Background(), time.Duration(timeout)*time.Second)
	x := make([]int, len(spn.Schema))
	for i := range x {
		x[i] = -1
	}
	return dfsFCnOnS(ctx, spn, x, baseline)
}

func dfsFCnOnS(ctx context.Context, spn SPN, x []int, baseline float64) float64 {
	select {
	case <-ctx.Done():
		return baseline
	default:
	}

	x2 := make([]int, len(x))
	copy(x2, x)
	x = x2
	var d [][]float64
	for {
		updated := false
		d = derivativeOfAssignmentX(spn, x)
		for i := range x {
			if x[i] == -1 {
				if d[i][0] <= baseline && d[i][1] <= baseline {
					return baseline
				}
				if d[i][0] <= baseline {
					x[i] = 1
					updated = true
				}
				if d[i][1] <= baseline {
					x[i] = 0
					updated = true
				}
			}
		}
		if !updated {
			break
		}
	}
	cnt := 0
	for i := range x {
		if x[i] == -1 {
			cnt++
		}
	}
	if cnt > 1 && len(x)-cnt >= 5 {
		spn = stage(spn, x)
		x = make([]int, len(spn.Schema))
		for i := range x {
			x[i] = -1
		}
		d = derivativeOfAssignmentX(spn, x)
	}
	varID := -1
	valID := -1
	for i := range x {
		if x[i] == -1 {
			var valI int
			if d[i][0] < d[i][1] {
				valI = 1
			} else {
				valI = 0
			}
			if varID == -1 || d[varID][valID] < d[i][valI] {
				varID = i
				valID = valI
			}
		}
	}
	if varID == -1 {
		return math.Max(baseline, d[0][x[0]])
	}
	if cnt == 1 {
		return d[varID][valID]
	}
	x[varID] = valID
	baseline = dfsFCnOnS(ctx, spn, x, baseline)
	x[varID] = 1 - valID
	baseline = dfsFCnOnS(ctx, spn, x, baseline)
	return baseline
}

func stage(spn SPN, q []int) SPN {
	idMap := map[int]int{}
	varCnt := 0
	schema := make([]int, 0, len(spn.Schema))
	for i, c := range q {
		if c == -1 {
			idMap[i] = varCnt
			varCnt++
			schema = append(schema, spn.Schema[i])
		}
	}
	if varCnt == 0 {
		log.Println(q)
		log.Fatal("q has no -1")
	}
	nn := len(spn.Nodes)
	ns := make([]Node, nn+1)
	we := make([]float64, nn)
	for i, n := range spn.Nodes {
		switch n := n.(type) {
		case *Trm:
			if q[n.Kth] == -1 {
				ns[i] = &Trm{Kth: idMap[n.Kth], Value: n.Value}
			} else {
				w := math.Inf(-1)
				if n.Value == 0 && q[n.Kth] == 0 {
					w = 0
				}
				if n.Value == 1 && q[n.Kth] == 1 {
					w = 0
				}
				we[i] = w
			}
		case *Sum:
			if ns[n.Edges[0].Node.ID()] == nil {
				we[i] = logSumExpF(len(n.Edges), func(k int) float64 {
					return n.Edges[k].Weight + we[n.Edges[k].Node.ID()]
				})
			} else {
				es := make([]SumEdge, len(n.Edges))
				for j, e := range n.Edges {
					es[j] = SumEdge{e.Weight + we[e.Node.ID()], ns[e.Node.ID()]}
				}
				ns[i] = &Sum{Edges: es}
			}
		case *Prd:
			es := make([]PrdEdge, 0, len(n.Edges))
			w := 0.0
			for _, e := range n.Edges {
				w += we[e.Node.ID()]
				if ns[e.Node.ID()] != nil {
					es = append(es, PrdEdge{ns[e.Node.ID()]})
				}
			}
			we[i] = w
			if len(es) > 0 {
				ns[i] = &Prd{Edges: es}
			}
		}
	}
	if _, ok := ns[nn-1].(*Sum); !ok {
		ns[nn] = &Sum{Edges: []SumEdge{{we[nn-1], ns[nn-1]}}}
	}
	nodes := make([]Node, 0, nn+1)
	for _, n := range ns {
		if n != nil {
			n.SetID(len(nodes))
			nodes = append(nodes, n)
		}
	}
	return SPN{nodes, schema}
}

func evalUncompletedX(spn SPN, x []int, xi int) float64 {
	a := make([][]float64, len(spn.Schema))
	for i := range a {
		a[i] = make([]float64, 2)
		if i < xi {
			a[i][x[i]] = 1
		} else {
			a[i][0] = 1
			a[i][1] = 1
		}
	}
	return spn.Eval(a)[len(spn.Nodes)-1]
}

func derivativeOfAssignmentX(spn SPN, x []int) [][]float64 {
	return derivativeOfAssignment(spn, X2Ass(x, spn.Schema))
}

func derivativeOfAssignment(spn SPN, ass [][]float64) [][]float64 {
	der := spn.Derivative(ass)
	d := make([][]float64, len(spn.Schema))
	for i := range d {
		d[i] = make([]float64, spn.Schema[i])
		for j := range d[i] {
			d[i][j] = math.Inf(-1)
		}
	}
	for i, n := range spn.Nodes {
		if n, ok := n.(*Trm); ok {
			d[n.Kth][n.Value] = logSumExp(d[n.Kth][n.Value], der[i])
		}
	}
	return d
}
