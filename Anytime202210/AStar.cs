using System;
using System.IO;
using System.Collections;
using Tanis.Collections;

namespace Huangbo.AStarPetri
{

    /// <summary>
    /// Base class for pathfinding nodes, it holds no actual information about the map. 
    /// An inherited class must be constructed from this class and all virtual methods must be 
    /// implemented. Note, that calling base() in the overridden methods is not needed.
    /// </summary>
 
    public class AStarNode : IComparable //A state node in the reachability graph of a Petri net
    {
        #region Properties

        public AStarNode Parent//parent node
        {
            set
            {
                FParent = value;
            }
            get
            {
                return FParent;
            }
        }
        private AStarNode FParent;

        public AStarNode GoalNode //goal node
        {
            set
            {
                FGoalNode = value;
            }
            get
            {
                return FGoalNode;
            }
        }
        private AStarNode FGoalNode;

        public decimal gValue //g value of a node (The accumulative cost of the path until now.)
        {
            set
            {
                FgValue = value;
            }
            get
            {
                return FgValue;
            }
        }
        private decimal FgValue;

        public decimal hValue //h value of a node (The estimated minmal cost to the goal from here.)
        {//h
            set
            {
                FhValue = value;
            }
            get
            {
                return FhValue;
            }
        }
        private decimal FhValue;

        public decimal fValue //f value of a node(f=g+h, representing an estimated of the lowest cost from the initial node to the goal along a path through the current node)
        {//f
            set
            {
                FfValue = value;
            }
            get
            {
                return FfValue;
            }
        }
        private decimal FfValue;

        public int[] M //the marking of node in the reachability graph
        {
            get
            {
                return FM;
            }
        }
        private int[] FM;

        public decimal[,] R //the token remaining time matrix of a place-timed Petri net
        {
            get
            {
                return FR;
            }
        }
        private decimal[,] FR;

        public int TFireFrom //the transition whose firing generates the node
        {
            get
            {
                return FTFireFrom;
            }
            set
            {
                FTFireFrom = value;
            }
        }
        private int FTFireFrom;

        public int[] EnabledTransitions //the set of transitions that are enabled at the node
        {
            get
            {
                return FEnabledTransitions;
            }
            set
            {
                Array.Copy(value, FEnabledTransitions, value.Length);
            }
        }
        private int[] FEnabledTransitions;

        public decimal MarkingDepth //the depth of the node, i.e., the number of transition firings from the initial node to the curren node
        {
            get
            {
                return FMarkingDepth;
            }
            set
            {
                FMarkingDepth = value;
            }
        }
        private decimal FMarkingDepth;

        public decimal hFCost  //the second h function may be used for nodes in OPEN
        {
            set
            {
                FhFCost = value;
            }
            get
            {
                return FhFCost;
            }
        }
        private decimal FhFCost;

        public decimal Delt//从父标识到某变迁实施得到本标识所用时间 
        { //Delt denotes the time needed by a parent node to become enabled and generate the current node. 
            set
            {
                FDelt = value;
            }
            get
            {
                return FDelt;
            }
        }
        private decimal FDelt;

        private decimal delt = 0;//变迁变为可发射所需时间

        // 通过变迁的发射而放入输出库所中的托肯必须等待一定时间后才可利用，并且该时间等于该库所的操作时间
        // M(k)- 和 Mr(k)- 分别表示：变迁发射前，那刻 "系统的标识" 和 "剩余处理时间矩阵"
        // M(k)+ 和 Mr(k)+ 分别表示：变迁发射后，输入托肯已移走但输出托肯还未加入时 "系统的标识" 和 "剩余处理时间矩阵"
        // M(k)- and Mr(k)- denote the marking and the token remaining time matrix before a transition fires, respectively.
        // M(k)+ denotes the marking after tokens are removed from the preplaces of a fired transition and before tokens are added into the postplace of the transition. 
        // Mr(k)+ denotes the token remaining time matrix after the transition fires.
        private int[] MF = new int[AStar.np];//M(k)-
        private int[] MZ = new int[AStar.np];//M(k)+
        private decimal[,] MrF = new decimal[AStar.np, AStar.MAX_TOK_PA];//Mr(k)- 
        public decimal[,] MrZ = new decimal[AStar.np, AStar.MAX_TOK_PA];//Mr(k)+	 

        #endregion


        #region Constructors
        //AStarNode(父节点, 目标节点, g值, h值, f值, 节点的标志, 该标识下所有库所的托肯剩余时间矩阵, 产生本标识所实施的变迁, 标识的深度,第二个h值，从父标识到变迁实施得到本标识所用时间)
        public AStarNode(AStarNode AParent, AStarNode AGoalNode, decimal AgValue, decimal AhValue, decimal AfValue, int[] AM, decimal[,] AMr, int ATFireFrom, decimal AMarkingDepth, decimal AhFCost, decimal ADelt)
        {
            FParent = AParent;
            FGoalNode = AGoalNode;
            FgValue = AgValue;
            FhValue = AhValue;
            FfValue = AfValue;
            FM = new int[AStar.np];
            Array.Copy(AM, FM, AM.Length);
            FR = new decimal[AStar.np,AStar.MAX_TOK_PA];
            Array.Copy(AMr, FR, AMr.Length);
            FTFireFrom = ATFireFrom;
            FEnabledTransitions = new int[AStar.nt];
            FMarkingDepth = AMarkingDepth;
            FhFCost = AhFCost;
            FDelt = ADelt;
        }
        #endregion

        #region Public Methods
        public bool IsGoal()//判断本节点的M和Mr(R)是否与GoalNode一致 //zzx
        {//Decide whether or not this node is the same as the goal node in terms of M and Mr(R). 
            if (IsSameStatePlusMr(FGoalNode) == false)//判断M和Mr(R)是否相等
                return false;
            return true;
        }

        public virtual bool IsSameState(AStarNode ANode)//判断某节点的标识M是否和本节点一致 //只判断M
        {//Decide whether or not this node is the same as the goal node only in terms of M.
            if (ANode == null)
                return false;
            if (FM.Length != ANode.FM.Length)
                return false;
            for (int i = 0; i < FM.Length; ++i)
                if (FM[i] != ANode.FM[i])
                    return false;
            return true;
        }

        public virtual bool IsSameStatePlusMr(AStarNode ANode)//判断ANode节点的M和Mr是否和本节点一致//判断M和Mr
        {//Decide whether or not this node is the same as the goal node in terms of M and Mr(R).
            if (ANode == null)
                return false;
            if (FM.Length != ANode.FM.Length)
                return false;
            for (int i = 0; i < FM.Length; ++i)
                if (FM[i] != ANode.FM[i])
                    return false;
            for (int i = 0; i < FR.GetLength(0); ++i)//zzx/////////////
                for (int j = 0; j < FR.GetLength(1); ++j)
                {
                    if (FR[i, j] != ANode.FR[i, j])
                        return false;
                }
            return true;
        }

        public virtual decimal CalculateH(int method, decimal ep2, decimal hValueStartNode)//Calculates the h value of a node, i.e., the estimated minimal cost of the path from the node to the goal.
        //h1=max{ei(m)} plus R; max{ei(m)} comes from Xiong98.
        //h2=0;
        //h4=-dep(m);       

        //h7 = h_H that is from Chapter 9 of our book;

        //h710(Pohl)=h+ep2*[1-depth(M)/N]*h, h=h7=h_H, 此时要设置总深度N=totalDepth！  大-小，线性
        //    (reversed Pohl)=h+ep2*[depth(M)/N]*h, h=h7=h_H, 此时要设置总深度N=totalDepth！   小-大，线性
        //    (Pohl)=h+ep2*[1-depth(M)/N]^2*h, h=h7=h_H, 此时要设置总深度N=totalDepth！   大-小，2次，凹
        //    (Pohl)=h+ep2*{1-[depth(M)/N]^2}*h, h=h7=h_H, 此时要设置总深度N=totalDepth！   大-小，2次，凸
        //    (Pohl)=h+ep2*{1-0.5*[1-depth(M)/N]}*h, 0<=1-depth(M)/N<0.4;        h=h7=h_H, 此时要设置总深度N=totalDepth！   大-小，线性，分段函数
        //          =h+ep2*{2-3*[1-depth(M)/N]}*h, 0.4<=1-depth(M)/N<0.6;       
        //          =h+ep2*{0.5-0.5*[1-depth(M)/N]}*h, 0.6<=1-depth(M)/N<=1;   

        //h720(IDWA)=h+ep2*(h/h_0)*h, h=h7=h_H,  大-小，线性
        //h721(IDWA)=h+ep2*[1-h/h_0]*h, h=h7=h_H,    小-大，线性
        //h722(IDWA)=h+ep2*[h/h_0]^2*h, h=h7=h_H,  大-小，2次，凹
        //h723(IDWA)=h+ep2*{1-[1-h/h_0]^2}*h, h=h7=h_H, 大-小，2次，凸

     

        //h9=hs+max{ei(m)}+he in which max{ei(m)} comes from Xiong98, hs denotes the necessary time before the resource is used, and he denotes the necessary time after the resource is used.
        {
            if (method == 1) //h1=max{ei(m)} plus R; max{ei(m)} comes from Xiong98.
            {
                /*
                 //===================================== start of New4x3 =====================================
                 const int ResNum = 3; //资源库所数量 the number of resource places
                 int[] ResourceTime = new int[ResNum];//每个资源库所的所有标识的剩余处理时间
                 for (int i = 0; i < ResourceTime.Length; ++i)
                 {
                     ResourceTime[i] = 0;
                 }

                 int[,] WOT =
                 {
                     {5,4,4},{0,4,4},{0,4,4},{0,0,4},{0,0,4},{0,0,0},{0,0,0},
                     {2,2,5},{2,0,5},{2,0,5},{2,0,0},{2,0,0},{0,0,0},{0,0,0},
                     {2,5,5},{2,5,0},{2,5,0},{0,5,0},{0,5,0},{0,0,0},{0,0,0},
                     {2,4,2},{2,4,0},{2,4,0},{2,0,0},{2,0,0},{0,0,0},{0,0,0},
                     {0,0,0},{0,0,0},{0,0,0}
                 };

                 //加Mr
                 for (int n = 0; n < AStar.np; ++n)
                    for (int m = 0; m < AStar.MAX_TOK_PA; ++m)
                    {
                     if (MrF[n,m] != 0)
                     {
                         if (n == 1 || n == 12 || n == 17 || n == 26)
                             ResourceTime[0] += (int)MrF[n,m];
                         else if (n == 3 || n == 8 || n == 19 || n == 24)
                             ResourceTime[1] += (int)MrF[n,m];
                         else if (n == 5 || n == 10 || n == 15 || n == 22)
                             ResourceTime[2] +=  (int)MrF[n,m];
                     }
                 }
                //===================================== end of New4x3 =====================================

                */

                //===================================== start of ChenFig5 =====================================
                const int ResNum = 6; //资源库所数量 the number of resource places

                decimal [] ResourceTime = new decimal[ResNum];
                for (int i = 0; i < ResourceTime.Length; ++i)                
                    ResourceTime[i] = 0;
                

                int[,] WOT =
                {
                  {0,0,3,0,7,5 }, {0,0,3,0,4,5 }, {0,0,3,0,4,5 }, {0,0,3,0,4,5 }, {0,0,3,0,0,5 }, {0,0,0,0,0,5 }, {0,0,0,0,0,0 },
                  {0,3,0,4,9,2 }, {0,3,0,4,9,0 }, {0,3,0,0,9,0 }, {0,3,0,0,5,0 }, {0,0,0,0,5,0 }, {0,0,0,0,0,0 }, {0,0,0,0,0,0 },
                  {0,0,0,0,0,0},  {0,0,0,0,0,0},  {0,0,0,0,0,0},  {0,0,0,0,0,0},  {0,0,0,0,0,0},  {0,0,0,0,0,0},  {0,0,0,0,0,0}

                 };

                //加Mr
                for (int n = 0; n < AStar.np; ++n)
                    for (int m = 0; m < AStar.MAX_TOK_PA; ++m)
                    {
                        if (MrF[n, m] != 0)
                        {
                            if (n == 3)//111这里3和9换了位置
                                ResourceTime[0] += (decimal)MrF[n, m]; //如果resource unit>1,用int是否合适？
                            else if (n == 11 || n == 2)
                                ResourceTime[1] += (decimal)MrF[n, m];//111 将int改为decimal
                            else if (n == 1 || n == 4 || n == 10 || n == 12)
                                ResourceTime[4] += (decimal)MrF[n, m];
                            else if (n == 6 || n == 8)
                                ResourceTime[5] += (decimal)MrF[n, m];
                            else if (n == 9)//111这里3和9换了位置
                                ResourceTime[3] += (decimal)MrF[n, m];
                            else if (n == 5)
                                ResourceTime[2] += (decimal)MrF[n, m];
                        }
                    }
                //===================================== end of ChenFig5 =====================================





                /*            
              
                      //===================================== start of ChenFig6 =====================================
                      const int ResNum = 7; //资源库所数量 the number of resource places
                      decimal [] ResourceTime = new decimal [ResNum];
                      for (int i = 0; i < ResourceTime.Length; ++i)
                      {
                          ResourceTime[i] = 0;
                      }

                      decimal  [,] WRT =
                      {
                              {0,7,0,0,2,0,0},{0,5,0,0,2,0,0},{0,5,0,0,0,0,0},{0,0,0,0,0,0,0},{3,3,4,0,0,0,0},{0,3,4,0,0,0,0},
                              {0,6,4,0,1,0,0},{0,0,4,0,1,0,0},{0,0,4,0,0,0,0},{0,0,0,0,0,0,0},{0,3,4,0,0,0,2},{0,0,4,0,0,0,2},
                              {0,0,4,0,0,0,0},{2,4,6,0,0,3,1.5},{2,4,0,0,0,3,1.5},{2,4,0,0,0,3,0},{2,0,0,0,0,3,0},{2,0,0,0,0,0,0},
                              {0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},
                              {0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0}
                      };

                     //加Mr
                     /*  for (int n = 0; n < AStar.np; ++n)
                           for (int m = 0; m < AStar.MAX_TOK_PA; ++m)
                           {
                               if (MrF[n, m] != 0)
                               {
                                   if (n == 5)
                                       ResourceTime[0] += (decimal)MrF[n, m];
                                   else if (n == 2 || n == 8)
                                       ResourceTime[1] += (decimal)MrF[n, m];
                                   else if (n == 10 || n == 17)
                                       ResourceTime[2] += (decimal)MrF[n, m];
                                   else if (n == 12 || n == 15)
                                       ResourceTime[3] += (decimal)MrF[n, m];
                                   else if (n == 5 || n == 18)
                                       ResourceTime[4] += (decimal)MrF[n, m];
                                   else if (n == 1 || n == 3 || n == 7 || n == 11 || n == 16)
                                       ResourceTime[5] += (decimal)MrF[n, m];
                                   else if (n == 9 || n == 14)
                                       ResourceTime[6] += (decimal)MrF[n, m];
                               }
                           }*/

                //===================================== end of ChenFig6 =====================================


                /*
                  //===================================== start of 1112 =====================================
                  const int ResNum = 2; //资源库所数量 the number of resource places
                  decimal[] ResourceTime = new decimal[ResNum];
                  for (int i = 0; i < ResourceTime.Length; ++i)
                  {
                      ResourceTime[i] = 0;
                  }

                  double[,] WRT = 
                  {
                          {1.5,2},{0,2},{0,0},{0,0},{2,1},
                          {2,0},{0,0},{0,0},{0,0},{0,0},
                  };

                  //加Mr
                /*  for (int n = 0; n < AStar.np; ++n)
                      for (int m = 0; m < AStar.MAX_TOK_PA; ++m)
                      {
                          if (MrF[n, m] != 0)
                          {
                              if (n == 1||n == 6)
                                  ResourceTime[0] += (decimal)MrF[n, m];
                              else if (n == 2 || n == 5 )
                                  ResourceTime[1] += (decimal)MrF[n, m];                        
                          }
                      }
                 //===================================== end of 1112 =====================================
             */


                /*
                 //===================================== start of xiong98 =====================================
                 const int ResNum = 3; //资源库所数量 the number of resource places
                 decimal[] ResourceTime = new decimal[ResNum];
                 for (int i = 0; i < ResourceTime.Length; ++i)
                 {
                     ResourceTime[i] = 0;
                 }

                  double[,] WRT =
                 {
                         {2,3,4},{0,3,4},{0,3,4},{0,0,4},{0,0,4},{0,0,0},{0,0,0},
                         {2,2,4},{2,2,0},{2,2,0},{0,2,0},{0,2,0},{0,0,0},{0,0,0},
                         {3,3,5},{0,3,5},{0,3,5},{0,3,0},{0,3,0},{0,0,0},{0,0,0},
                         {3,3,4},{3,0,4},{3,0,4},{3,0,0},{3,0,0},{0,0,0},{0,0,0},
                         {0,0,0},{0,0,0},{0,0,0}
                     };

             /*     double[,] WRT =
                 {
                         {2,1.5,4},{0,1.5,4},{0,1.5,4},{0,0,4},{0,0,4},{0,0,0},{0,0,0},
                         {2,1,4},{2,1,0},{2,1,0},{0,1,0},{0,1,0},{0,0,0},{0,0,0},
                         {3,1.5,5},{0,1.5,5},{0,1.5,5},{0,1.5,0},{0,1.5,0},{0,0,0},{0,0,0},
                         {3,1.5,4},{3,0,4},{3,0,4},{3,0,0},{3,0,0},{0,0,0},{0,0,0},
                         {0,0,0},{0,0,0},{0,0,0}
                     };*/

                //加Mr
                /* for (int n = 0; n < AStar.np; ++n)
                       for (int m = 0; m < AStar.MAX_TOK_PA; ++m)
                       {
                       if (MrF[n,m] != 0)
                       {
                           if (n == 1 || n == 10 || n == 15 || n == 26)
                               ResourceTime[0] += (int)MrF[n,m];
                           else if (n == 3 || n == 12 || n == 19 || n == 22)
                               ResourceTime[1] += (int)MrF[n,m];
                           else if (n == 5 || n == 8 || n == 18 || n == 24)
                               ResourceTime[2] += (int)MrF[n,m];
                       }
                   }*/
                //===================================== end of xiong98 =====================================



                for (int n = 0; n < AStar.np; ++n)
                {
                    if (MF[n] != 0)
                    {
                        for (int x = 0; x < ResNum; ++x)
                        {
                            ResourceTime[x] += MF[n] * WOT[n, x];
                        }
                    }
                }
                
                decimal max = 0;
                for (int i = 0; i < ResourceTime.Length; ++i)
                {
                    if (max < ResourceTime[i])
                    {
                        max = ResourceTime[i];
                    }
                }
                return max;
            }


            if (method == 2)
            {
                return 0;
            }

            if (method == 4)
            {
                return (-(FMarkingDepth + 1));
            }

           
            if (method == 7)  
            //h7=h_H comes from Eq.(9.2) in Chapter 9 of our book. It is an admissible and highly informed heuristic function that can be used for the nets with alternative routings, weighted arcs, and multiple resource copies.     
            //Before h7=h_H is used, the number of resource places, the WRT matrix, the Upi matrix, and the M0r vector of the Petri net should be given in the class AStar. 
            //WRT denotes the weighted remaining time whose definition is given in Chapter 9 of our book. Note that MRT only consider non-resource places.
            //Upi(r) denotes the units of r that are required by the operation denoted by the place pi. Note that Upi only consider non-resource places.
            //M0r denotes the number of tokens in each resource place at the initial marking.
            {

                decimal[] ResourceTime = new decimal[AStar.ResNum];
                for (int i = 0; i < ResourceTime.Length; ++i)
                    ResourceTime[i] = 0;                       
               

                //h7=h_H
                for (int n = 0; n < AStar.np - AStar.nrs; ++n) //for each non-resource place
                {
                    //取p_i中所有非零剩余时间之和
                    decimal temp = 0;
                    for (int t = 0; t < AStar.MAX_TOK_PA; t++)
                    {
                        temp += MrF[n, t];
                    }

                    if (MF[n] != 0)
                    {
                        for (int x = 0; x < AStar.ResNum; ++x)
                        {
                            ResourceTime[x] += MF[n] * (decimal)AStar.WRT[n, x];
                            ResourceTime[x] += temp * (decimal)AStar.Upi[n, x] / AStar.M0r[x];
                        }
                    }
                }

                //h=max_i
                decimal max = 0;
                for (int i = 0; i < ResourceTime.Length; ++i)
                {
                    if (max < ResourceTime[i])
                    {
                        max = ResourceTime[i];
                    }
                }
               

                //  max = max1 + ep2 * (1 - ((float)FMarkingDepth + 1) /32) * max1;//！！！！要修改总的深度！！！！！原函数
                // max= max1+ep2 * (System.Math.Sqrt(max1 / hValueStartNode)) * max1;
                //max = max1 + ep2 * (max1 / hValueStartNode) * max1;
                //   max = max1+ep2*Math.Pow(max1 / hValueStartNode, 1.0/4)* max1;//开方函数                
                //  Console.Write(Math.Round(1 - ((float)FMarkingDepth + 1) / 72,2));
                // Console.WriteLine();
                //max为h(M)=max{ei(m)}的值，72为N总深度72=24*3，chenfig6222 32  ,xiong983333   72   ,ChenFig566   72,New4x3_1111  24
                //  max = max1 + ep2 * (1- System.Math.Abs(2 * ((float)FMarkingDepth + 1) / 72 - 1)) * max1;//这里陷入无解状态，出不来结果//绝对值函数
                //max = max1+ep2*Math.Pow(((float)FMarkingDepth + 1) / 72 - 1,2)* max1;//开方函数
                /*Console.Write(Math.Round(1 - System.Math.Abs(2 * ((float)FMarkingDepth + 1) / 72- 1), 2));
                  Console.WriteLkine();*/
                // Console.Write(Math.Round(Math.Pow(((float)FMarkingDepth + 1) / 72 - 1, 2), 2));
                //  Console.WriteLine();
                //  max = max1 + ep2 * (System.Math.Sqrt(1 - ((float)FMarkingDepth + 1) / 72)) * max1;//开平方函数
                //  max = max1 + ep2 * (System.Math.Pow(1 - ((float)FMarkingDepth + 1) / 72,1.0/4)) * max1;//开随意平方函数
                //   Console.Write(Math.Round(System.Math.Sqrt(1 - ((float)FMarkingDepth + 1) / 72),2));
                //  Console.WriteLine();
                //     if(FMarkingDepth <=0.5*32)//分段函数
                //       max = max1 + ep2 * (System.Math.Sqrt(1 - ((float)FMarkingDepth + 1) / 32)) * max1;
                //  else
                //  max = max1 + ep2 * ( 0.707*System.Math .Abs(Math.Log(((float)FMarkingDepth + 1) / 32,2))) * max1;
                //log函数不可取，因为log函数的真数不能为0
                return max;
            }

            
            if (method == 710)
            //h710(Pohl: dynamic weighting)=h+ep2*[1-depth(M)/N]*h, h=h7=h_H, 此时要在AStar.cs中设置总深度N=totalDepth！  大-小，线性
            //Before h710 is used, the number of resource places, the WRT matrix, the Upi matrix, and the M0r vector of the Petri net should be given in the class AStar. 
                //需要选择所用的Petri网，以便自动计算深度totalDepth
            {
                decimal[] ResourceTime = new decimal[AStar.ResNum];
                for (int i = 0; i < ResourceTime.Length; ++i)
                    ResourceTime[i] = 0;


                //h7=h_H
                for (int n = 0; n < AStar.np - AStar.nrs; ++n) //for each non-resource place
                {
                    //取p_i中所有非零剩余时间之和
                    decimal temp = 0;
                    for (int t = 0; t < AStar.MAX_TOK_PA; t++)
                    {
                        temp += MrF[n, t];
                    }

                    if (MF[n] != 0)
                    {
                        for (int x = 0; x < AStar.ResNum; ++x)
                        {
                            ResourceTime[x] += MF[n] * (decimal)AStar.WRT[n, x];
                            ResourceTime[x] += temp * (decimal)AStar.Upi[n, x] / AStar.M0r[x];
                        }
                    }
                }

                //max=h_H
                decimal max = 0;
                for (int i = 0; i < ResourceTime.Length; ++i)
                {
                    if (max < ResourceTime[i])
                    {
                        max = ResourceTime[i];
                    }
                }

                //For ChenFig5 and its variants！！！！！！！
                decimal totalDepth=7*(AStar.StartM[0]+AStar.StartM[7]); //p0和p8为start places

                //For ChenFig6 and its variants！！！！！！！
                //decimal totalDepth = 4 * AStar.StartM[0] + 6 * AStar.StartM[4] + 6 * AStar.StartM[13]; //p1,p5和p14为start places

                
                decimal dndG = Math.Round ((FMarkingDepth + 1) / totalDepth,3);  //结果为小数的乘除，操作数都要为decimal，否则结果0.2会成为0





                //decimal final = max + (decimal)ep2 * (1 - dndG) * max;  //(Pohl: dynamic weighting)=h+ep2*[1-dn/dG]*h, h=h7=h_H, 此时要设置总深度N=dG=totalDepth！  大-小，(1+ep2)*h->h，线性

                /*
                decimal final;
                if (ep2 != 0)
                    final = max + (decimal)ep2 * (1 - (1 + Math.Round(1 / (decimal)ep2, 2)) * dndG) * max;  //(Pohl: dynamic weighting to 0)=h+ep2*[1-(1+1/ep2)dn/dG]*h, h=h7=h_H, 此时要设置总深度N=dG=totalDepth！  大-小，(1+ep2)*h->0(ep2=1时减到0)，线性
                else
                    final = max;
               */  
               

                //decimal final = max + (decimal)ep2 * dndG * max;  //(reversed Pohl: dynamic weighting)=h+ep2 * (dn/dG) *h, h=h7=h_H, 此时要设置总深度N=dG=totalDepth！  小-大，线性


                decimal final = max + (decimal)ep2 * (decimal)Math.Round(Math.Pow( 1 - (double)dndG, 2),2) * max;  //(Pohl)=h+ep2*[1-dn/dG]^2*h, h=h7=h_H, 此时要设置总深度N=dG=totalDepth！   大-小，2次，凹

                //decimal final = max + (decimal)ep2 * (decimal)Math.Round(1 - Math.Pow((double)dndG, 2), 2) * max;  //(Pohl)=h+ep2*{1-[dn/dG]^2}*h, h=h7=h_H, 此时要设置总深度N=dG=totalDepth！   大-小，2次，凸


                /*
                //    (Pohl)=h+ep2*{1-0.5*[1-dndG]}*h,      0<= dn/dG <0.4;        h=h7=h_H, 此时要设置总深度dG=totalDepth！   大-小，线性，分3段函数
                //          =h+ep2*{2-3*[1-dndG]}*h,        0.4<= dn/dG <0.6;       
                //          =h+ep2*{0.5-0.5*[1-dndG]}*h,    0.6<= dn/dG <=1;
                decimal final;
                if (dndG>=0m && dndG<0.4m)
                    final = max + (decimal)ep2 * (1 - (decimal)0.5*dndG) * max;  
                else if(dndG>=0.4m && dndG<0.6m)
                    final = max + (decimal)ep2 * (2 - (decimal)3 * dndG) * max;
                else
                    final = max + (decimal)ep2 * ((decimal)0.5 - (decimal)0.5 * dndG) * max;
                */ 

                
                /*
                //    (Pohl)=h+ep2*h,               0<= dn/dG <0.5;        h=h7=h_H, 此时要设置总深度dG=totalDepth！   大-小，线性，分2段函数
                //          =h+ep2*(2-2*dndG)*h,    0.5<= dn/dG <=1;   
                decimal final;
                if (dndG >= 0m && dndG < 0.5m)
                    final = max + (decimal)ep2 * max;  
                else
                    final = max + (decimal)ep2 * (2 - (decimal)2 * dndG) * max;
                */

                /*
                //    (Pohl)=h+ep2*2*dn/dG*h,       0<= dn/dG <0.5;        h=h7=h_H, 此时要设置总深度dG=totalDepth！   小-大-小，线性，分2段函数
                //          =h+ep2*(2-2*dndG)*h,    0.5<= dn/dG <=1;   
                decimal final;
                if (dndG >= 0m && dndG < 0.5m)
                    final = max + (decimal)ep2 * 2 * dndG * max;
                else
                    final = max + (decimal)ep2 * (2 - (decimal)2 * dndG) * max;
                */


                
                return final;//                
            }

            
            
            if (method == 9)//该h函数为改进xiong98即添加hs和he两个部分  zhaozhixia  
            //h9=hs+max{ei(m)}+he in which max{ei(m)} comes from Xiong98, hs denotes the necessary time before the resource is used, and he denotes the necessary time after the resource is used.
            {

                //===================================== start of xiong98 =====================================
                const int ResNum = 3; //三个资源库所
                int[] ResourceTime = new int[ResNum];
                int[] MachineTime2 = new int[ResNum];
                int[] MachineTime3 = new int[ResNum];
                for (int i = 0; i < ResourceTime.Length; ++i)
                {
                    ResourceTime[i] = 0;
                }
                for (int i = 0; i < MachineTime2.Length; ++i)
                {
                    MachineTime2[i] = 0;
                }
                for (int i = 0; i < MachineTime3.Length; ++i)
                {
                    MachineTime3[i] = 0;
                }

                //=============== start of 原xiong98 =================
                int[,] RST =
                    {
                   {2,3,4},{0,3,4},{0,3,4},{0,0,4},{0,0,4},{0,0,0},{0,0,0},
                   {2,2,4},{2,2,0},{2,2,0},{0,2,0},{0,2,0},{0,0,0},{0,0,0},
                   {3,3,5},{0,3,5},{0,3,5},{0,3,0},{0,3,0},{0,0,0},{0,0,0},
                   {3,3,4},{3,0,4},{3,0,4},{3,0,0},{3,0,0},{0,0,0},{0,0,0},
                   {0,0,0},{0,0,0},{0,0,0}//原xiong98
                   };
                //原xiong98
                int[,] hs = { { 0, -1, -1, -1, -1, -1, -1, 4, 0, 0, -1, -1, -1, -1, 0, -1, -1, -1, -1, -1, -1,  7, 4, 4, 0, 0, -1, -1 },
                                      { 2, 0, 0, -1, -1, -1, -1, 6, 2, 2, 0, 0, -1, -1, 8, 5, 5, 0, 0, -1, -1, 0,-1,-1,-1,-1,-1,-1 },
                                      { 5, 3, 3, 0, 0, -1, -1, 0, -1, -1, -1, -1, -1, -1, 3, 0, 0, -1, -1, -1, -1, 3, 0, 0, -1, -1, -1, -1 }};
                //    int[,] he = { { 7, 7, 7, 4, 4, 0, 0, 2, 2, 2, 2, 2, 0, 0, 8, 8, 8, 3, 3, 0, 0,0,0,0,0,0, 0, 0 } ,
                //                     { 4, 4, 4, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  7, 7, 7, 3, 3, 0, 0 } ,
                //                    { 0, 0, 0, 0, 0, 0, -1, 4, 4, -1,-1, -1, -1, -1, 3, 3, 3, 3, -1, -1, -1, 3, 3, 3, 3, -1, -1, -1 }};
                //   int[,] he = { { 7, -1, -1, -1, -1, -1, -1, 2, 2, 2, -1, -1, -1, -1, 8, -1, -1, -1, -1, -1, -1,0,0,0,0,0,-1,-1 },
                //                   {4,4,4,-1,-1,-1,-1,0,0,0,0,0,-1,-1,0,0,0,0,0,-1,-1,7, -1, -1, -1, -1, -1, -1 },
                //                   {0,0,0,0,0,-1,-1,4,-1,-1,-1,-1,-1,-1,3,3,3,-1,-1,-1,-1,3,3,3,-1,-1,-1,-1 } };
                int[,] he = { { 7, 7, -1, -1, -1, -1, -1, 2, 2, 2, 2, -1, -1, -1, 8, 8, -1, -1, -1, -1, -1,0,0,0,0,0,0,-1 },
                                 {4,4,4,4,-1,-1,-1,0,0,0,0,0,0,-1,0,0,0,0,0,0,-1,7, 7, -1, -1, -1, -1, -1 },
                                 {0,0,0,0,0,0,-1,4,4,-1,-1,-1,-1,-1,3,3,3,3,-1,-1,-1,3,3,3,3,-1,-1,-1 } };
                //=============== end of 原xiong98 =================

                /*
                //========= strat of 改xiong98 （m1 m2在job4上交换）======
                int[,] RST =
                  {
                    {2,3,4},{0,3,4},{0,3,4},{0,0,4},{0,0,4},{0,0,0},{0,0,0},
                    {2,2,4},{2,2,0},{2,2,0},{0,2,0},{0,2,0},{0,0,0},{0,0,0},
                    {3,3,5},{0,3,5},{0,3,5},{0,3,0},{0,3,0},{0,0,0},{0,0,0},
                    {3,3,4},{0,3,4},{0,3,4},{0,3,0},{0,3,0},{0,0,0},{0,0,0},
                    {0,0,0},{0,0,0},{0,0,0}///xiong98改动m1 m2  job4
                };
                //job4的xiong98m1和m2交换
                int[,] hs = { { 0, -1, -1, -1, -1, -1, -1, 4, 0, 0, -1, -1, -1, -1, 0, -1, -1, -1, -1, -1, -1,  0,-1,-1,-1,-1,-1,-1 },
                                   { 2, 0, 0, -1, -1, -1, -1, 6, 2, 2, 0, 0, -1, -1, 8, 5, 5, 0, 0, -1, -1,7, 4, 4, 0, 0, -1, -1 },
                                   { 5, 3, 3, 0, 0, -1, -1, 0, -1, -1, -1, -1, -1, -1, 3, 0, 0, -1, -1, -1, -1, 3, 0, 0, -1, -1, -1, -1 }};
                int[,] he = { { 7, 7, -1, -1, -1, -1, -1, 2, 2, 2, 2, -1, -1, -1, 8, 8, -1, -1, -1, -1, -1,7, 7, -1, -1, -1, -1, -1 },
                              {4,4,4,4,-1,-1,-1,0,0,0,0,0,0,-1,0,0,0,0,0,0,-1,0,0,0,0,0,0,-1 },
                              {0,0,0,0,0,0,-1,4,4,-1,-1,-1,-1,-1,3,3,3,3,-1,-1,-1,3,3,3,3,-1,-1,-1 } };
                //======= end of 改xiong98 （m1 m2在job4上交换）=========
                */
                /*
                //=============== strat of 改xiong98 （m1 m3在job3上交换）=================
                int[,] RST =
                {
                    {2,3,4},{0,3,4},{0,3,4},{0,0,4},{0,0,4},{0,0,0},{0,0,0},
                    {2,2,4},{2,2,0},{2,2,0},{0,2,0},{0,2,0},{0,0,0},{0,0,0},
                    {5,3,3},{5,3,0},{5,3,0},{0,3,0},{0,3,0},{0,0,0},{0,0,0},
                    {3,3,4},{3,0,4},{3,0,4},{3,0,0},{3,0,0},{0,0,0},{0,0,0},
                    {0,0,0},{0,0,0},{0,0,0}//m1  m3 job
                };
                //xiong98改进图m1 m3在job3交换
                  int[,] hs = { { 0, -1, -1, -1, -1, -1, -1, 4, 0, 0, -1, -1, -1, -1, 3, 0, 0, -1, -1, -1, -1, 7, 4, 4, 0, 0, -1, -1 } ,
                              { 2, 0, 0, -1, -1, -1, -1, 6, 2, 2, 0, 0, -1, -1, 8, 5, 5, 0, 0, -1, -1, 0,-1,-1,-1,-1,-1,-1 },
                                     { 5, 3, 3, 0, 0, -1, -1, 0, -1, -1, -1, -1, -1, -1, 0, -1, -1, -1, -1, -1, -1,3, 0, 0, -1, -1, -1, -1 }};
                  int[,] he = { { 7, 7, -1, -1, -1, -1, -1, 2, 2, 2, 2, -1, -1, -1, 3,3,3,3,-1,-1,-1,0,0,0,0,0,0,-1 },
                                {4,4,4,4,-1,-1,-1,0,0,0,0,0,0,-1,0,0,0,0,0,0,-1,7, 7, -1, -1, -1, -1, -1 },
                                {0,0,0,0,0,0,-1,4,4,-1,-1,-1,-1,-1,8, 8, -1, -1, -1, -1, -1,3,3,3,3,-1,-1,-1 } };
                //=============== end of 改xiong98 （m1 m3在job3上交换）=================
                */
                /*
                //=============== strat of 改xiong98 （平行）=================
                int[,] RST =
                {
                    {2,3,4},{0,3,4},{0,3,4},{0,0,4},{0,0,4},{0,0,0},{0,0,0},
                    {4,2,2},{0,2,2},{0,2,2},{0,0,2},{0,0,2},{0,0,0},{0,0,0},
                    {3,5,3},{0,5,3},{0,5,3},{0,0,3},{0,0,3},{0,0,0},{0,0,0},
                    {3,4,3},{0,4,3},{0,4,3},{0,0,3},{0,0,3},{0,0,0},{0,0,0},
                    {0,0,0},{0,0,0},{0,0,0}////平行xiong98
                };
                  int[,] hs = { { 0, -1, -1, -1, -1, -1, -1, 0, -1, -1, -1, -1, -1, -1, 0, -1, -1, -1, -1, -1, -1, 0, -1, -1, -1, -1, -1, -1 },
                { 2, 0, 0, -1, -1, -1, -1, 4, 0, 0, -1, -1, -1, -1,3, 0, 0, -1, -1, -1, -1,3, 0, 0, -1, -1, -1, -1 },
               { 5, 3, 3, 0, 0, -1, -1,  6, 2, 2, 0, 0, -1, -1, 8, 5, 5, 0, 0, -1, -1,7, 4, 4, 0, 0, -1, -1} };
                int[,] he = { { 7, 7, -1, -1, -1, -1, -1, 4, 4, -1, -1, -1, -1, -1, 8, 8, -1, -1, -1, -1, -1, 7, 7, -1, -1, -1, -1, -1 },
               {4,4,4,4,-1,-1,-1, 2, 2, 2, 2, -1, -1, -1,3,3,3,3,-1,-1,-1,3,3,3,3,-1,-1,-1 },
                {0,0,0,0,0,0,-1,0,0,0,0,0,0,-1,0,0,0,0,0,0,-1,0,0,0,0,0,0,-1 }};//平行xiong98
                //=============== end of 改xiong98 （平行）=================
                */
                //加Mr
                /*   for (int n = 0; n < AStar.np; ++n)
                   {
                       if (MrF[n] != 0)
                       {
                           if (n==1||n==10||n==15||n==22)
                               ResourceTime[0] += (int)MrF[n];
                           else if (n == 3 || n == 12 || n == 19 || n == 26)
                               ResourceTime[1] += (int)MrF[n];
                           else if (n == 5 || n == 8 || n == 18 || n == 24)
                               ResourceTime[2] += (int)MrF[n];
                       }
                   }*/
                //===================================== start of xiong98 =====================================
                /*
                //===================================== start of New4x3 =====================================
                const int ResNum = 3; //三个资源库所
                int[] ResourceTime = new int[ResNum];
                int[] MachineTime2 = new int[ResNum];
                int[] MachineTime3 = new int[ResNum];
                for (int i = 0; i < ResourceTime.Length; ++i)
                {
                    ResourceTime[i] = 0;
                }
                for (int i = 0; i < MachineTime2.Length; ++i)
                {
                    MachineTime2[i] = 0;
                }
                for (int i = 0; i < MachineTime3.Length; ++i)
                {
                    MachineTime3[i] = 0;
                }

             int[,] RST =
               {
                 {5,4,4},{0,4,4},{0,4,4},{0,0,4},{0,0,4},{0,0,0},{0,0,0},
                 {2,2,5},{2,0,5},{2,0,5},{2,0,0},{2,0,0},{0,0,0},{0,0,0},
                 {2,5,5},{2,5,0},{2,5,0},{0,5,0},{0,5,0},{0,0,0},{0,0,0},
                 {2,4,2},{2,4,0},{2,4,0},{2,0,0},{2,0,0},{0,0,0},{0,0,0},
                 {0,0,0},{0,0,0},{0,0,0}
               };

                //加Mr
             /*   for (int n = 0; n < AStar.np; ++n)
                {
                    if (MrF[n] != 0)
                     {
                        if (n == 1 || n == 12 || n == 17 || n == 26)
                            ResourceTime[0] += (int)MrF[n];
                        else if (n == 3 || n == 8 || n == 19 || n == 24)
                            ResourceTime[1] += (int)MrF[n];
                        else if (n == 5 || n == 10 || n == 15 || n == 22)
                            ResourceTime[2] += (int)MrF[n];
                     }
                }*/
                /*    int[,] hs={{0,-1,-1,-1,-1,-1,-1,7,5,5,0,0,-1,-1,5,0,0,-1,-1,-1,-1,6,4,4,0,0,-1,-1},
                              {5,0,0,-1,-1,-1,-1,0,-1,-1,-1,-1,-1,-1,7,2,2,0,0,-1,-1,2,0,0,-1,-1,-1,-1},
                              {9,4,4,0,0,-1,-1,2,0,0,-1,-1,-1,-1,0,-1,-1,-1,-1,-1,-1,0,-1,-1,-1,-1,-1,-1}};
                    int[,] he={{8,8,-1,-1,-1,-1,-1,0,0,0,0,0,0,-1,5,5,5,5,-1,-1,-1,0,0,0,0,0,0,-1},
                               {4,4,4,4,-1,-1,-1,7,7,-1,-1,-1,-1,-1,0,0,0,0,0,0,-1,2,2,2,2,-1,-1,-1},
                               {0,0,0,0,0,0,-1,2,2,2,2,-1,-1,-1,7,7,-1,-1,-1,-1,-1,6,6,-1,-1,-1,-1,-1} };
                     //===================================== end of New4x3 =====================================
                     */
                /*
               //===================================== start of ChenFig5 =====================================
               const int ResNum = 6; //六个资源库所
           int[] ResourceTime = new int[ResNum];
           int[] MachineTime2 = new int[ResNum];
           int[] MachineTime3 = new int[ResNum];
           for (int i = 0; i < ResourceTime.Length; ++i)
           {
               ResourceTime[i] = 0;
           }
           for (int i = 0; i < MachineTime2.Length; ++i)
           {
               MachineTime2[i] = 0;
           }
           for (int i = 0; i < MachineTime3.Length; ++i)
           {
               MachineTime3[i] = 0;
           }
           int[,] RST =
               {
                   {0,0,7,5,0,3},{0,0,4,5,0,3},{0,0,4,5,0,3}, {0,0,4,5,0,3}, {0,0,0,5,0,3}, {0,0,0,5,0,0}, {0,0,0,0,0,0},
                   {4,3,9,2,0,0}, {4,3,9,0,0,0}, {0,3,9,0,0,0},{0,3,5,0,0,0}, {0,0,5,0,0,0}, {0,0,0,0,0,0}, {0,0,0,0,0,0},
                   {0,0,0,0,0,0},{0,0,0,0,0,0}, {0,0,0,0,0,0},{0,0,0,0,0,0},  {0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0},   
               };
           int[,] hs ={{-1,-1,-1,-1,-1,-1,-1,2,0,-1,-1,-1,-1,-1,-1},
                         {3,0,-1,-1,-1,-1,-1,10,8,4,0,-1,-1,-1,-1},
                         {0,2,0,0,-1,-1,-1,6,4,0,3,0,-1,-1,-1 },
                         { 12,9,7,7,3,0,-1,0,-1,-1,-1,-1,-1,-1,-1},
                         {3,0, -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
                         {9,6,4,4,0,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1}};
           int[,] he = { { -1,-1,-1,-1,-1,-1,-1,12,12,12,-1,-1,-1,-1,-1},
                         {12,12,12,-1,-1,-1,-1,5,5,5,5,5,-1,-1,-1 },
                          {8,8,8,8,8,-1,-1,0,0,0,0,0,0,-1,-1 },
                          {0,0,0,0,0,0,0,16,16,-1,-1,-1,-1,-1,-1 },
                          {12,12,-1,12,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1 },
                           {5,5,5,5,5,5,-1,-1,-1,-1,-1,-1,-1,-1,-1 }};
           //===================================== end of ChenFig5 =====================================                 
           */
                /*
                //===================================== start of ChenFig6111 =====================================
                const int ResNum = 7; //7个资源库所
                int[] ResourceTime = new int[ResNum];
                int[] MachineTime2 = new int[ResNum];
                int[] MachineTime3 = new int[ResNum];
                for (int i = 0; i < ResourceTime.Length; ++i)
                {
                    ResourceTime[i] = 0;
                }
                for (int i = 0; i < MachineTime2.Length; ++i)
                {
                    MachineTime2[i] = 0;
                }
                for (int i = 0; i < MachineTime3.Length; ++i)
                {
                    MachineTime3[i] = 0;
                }
                int[,] RST=
                {
                         {0,7,0,0,4,0,0},{0,5,0,0,4,0,0},{0,5,0,0,0,0,0},{0,0,0,0,0,0,0},{3,3,4,0,0,0,0},{0,3,4,0,0,0,0},
                         {0,6,4,0,2,0,0},{0,0,4,0,2,0,0},{0,0,4,0,0,0,0},{0,0,0,0,0,0,0},{0,3,4,0,0,0,4},{0,0,4,0,0,0,4},
                         {0,0,4,0,0,0,0},{2,4,6,0,0,6,3},{2,4,0,0,0,6,3},{2,4,0,0,0,6,0},{2,0,0,0,0,6,0},{2,0,0,0,0,0,0},
                         {0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},
                         {0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0},{0,0,0,0,0,0,0}
                 };
                int[,] hs = { { -1,-1,-1,-1,0,-1,-1,-1,-1,-1,-1,-1,-1,19,13,10,6,0,-1,-1,-1,-1},
                              {0,4,0,-1,4,1,0,-1,-1,-1,0,-1,-1,9,3,0,-1,-1,-1,-1,-1,-1 },
                               {-1,-1,-1,-1,11,8,8,2,0,-1,7,4,0,0,-1,-1,-1,-1,-1,-1,-1,-1 },
                               {-1,-1,-1,-1,3,0,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1 },
                               { 2,0,-1,-1,11,8,6,0,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
                               { -1,-1,-1,-1,3,0,-1,-1,-1,-1,-1,-1,-1,13,7,4,0,-1,-1,-1,-1,-1},
                               {-1,-1,-1,-1,7,4,-1,-1,-1,-1,3,0,-1,6,0,-1,-1,-1,-1,-1,-1,-1 } };
                /*  int[,] he = { { -1,-1,-1,-1,12,12,-1,-1,-1,-1,-1,-1,-1,0,0,0,0,0,0,-1,-1,-1},
                                {0,0,0,0,6,6,6,6,-1,-1,8,8,-1,8,8,8,8,-1,-1,-1,-1,-1 },
                                 {-1,-1,-1,-1,0,0,0,0,0,0,0,0,0,15,15,-1,-1,-1,-1,-1,-1,-1 },
                                  { -1,-1,-1,-1,12,12,12,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
                                 {5,5,5,-1,4,4,4,4,4,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1 },
                                  {-1,-1,-1,-1,11,11,-1,-1,-1,-1,11,-1,-1,2,2,2,2,2,-1,-1,-1,-1 },
                                  {-1,-1,-1,-1,4,4,-1,-1,-1,-1,4,4,4,12,12,12,-1,-1,-1,-1,-1,-1 }};*/
                /*     int[,] he = { { -1,-1,-1,-1,-1,12,-1,-1,-1,-1,-1,-1,-1,0,0,0,0,0,-1,-1,-1,-1},
                                   {0,-1,0,-1,6,6,6,-1,-1,-1,8,-1,-1,8,8,8,-1,-1,-1,-1,-1,-1 },
                                    {-1,-1,-1,-1,0,0,0,0,0,-1,0,0,0,15,-1,-1,-1,-1,-1,-1,-1,-1 },
                                     { -1,-1,-1,-1,12,12,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1},
                                    {5,5,-1,-1,4,4,4,4,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1 },
                                     {-1,-1,-1,-1,11,11,-1,-1,-1,-1,-1,-1,-1,2,2,2,2,-1,-1,-1,-1,-1 },
                                     {-1,-1,-1,-1,4,4,-1,-1,-1,-1,4,4,-1,12,12,-1,-1,-1,-1,-1,-1,-1 }};
                     //===================================== start of ChenFig6111 =====================================
                     */
                //通用
                int k = 0;
                int s = 0;
                int min2 = 0;
                int min3 = 0;//max2为资源m3对应的各个库所的等待时间
                for (int m = 0; m < AStar.nrs; ++m)
                {
                    for (int n = 0; n < AStar.np - AStar.nrs; ++n)
                    {
                        if (MF[n] != 0)
                        {
                            ResourceTime[m] += MF[n] * RST[n, m];
                        }
                    }
                    for (int n = 0; n < AStar.np - AStar.nrs; ++n)
                    {
                        if (MF[n] != 0)
                        {

                            if (hs[m, n] != -1)
                            {
                                min2 = hs[m, n];
                                k = n;
                                break;
                            }

                        }
                    }
                    for (int n = k + 1; n < AStar.np - AStar.nrs; ++n)
                    {
                        if (MF[n] != 0)
                        {
                            if (hs[m, n] != -1)
                            {
                                if (min2 > hs[m, n])
                                    min2 = hs[m, n];//此处取目前状态下对应等待时间的最小值
                            }
                        }
                    }

                    for (int n = 0; n < AStar.np - AStar.nrs; ++n)
                    {
                        if (MF[n] != 0)
                        {
                            if (he[m, n] != -1)
                            {
                                min3 = he[m, n];
                                s = n;
                                break;
                            }

                        }
                    }
                    for (int n = s + 1; n < AStar.np - AStar.nrs; ++n)
                    {
                        if (MF[n] != 0)
                        {
                            if (he[m, n] != -1)
                            {
                                if (min3 > he[m, n])
                                    min3 = he[m, n];//此处取目前状态下对应等待时间的最小值
                            }
                        }
                    }
                    MachineTime2[m] = min2;
                    MachineTime3[m] = min3;
                }

                decimal max = 0;
                for (int i = 0; i < ResourceTime.Length; ++i)
                {
                    if (max < ResourceTime[i] + MachineTime2[i] + MachineTime3[i])
                    {
                        max = ResourceTime[i] + MachineTime2[i] + MachineTime3[i];
                    }

                }
                decimal max1 = 0;
                //======xiong98=======
                max1 = max + ep2 * (max / hValueStartNode) * max;// +max2 +max3;

                return max1;

            }



            return 0;
        }

        public virtual decimal CalculateHF(int method) // calculate the second heursitic value for nodes in OPEN; only applicable to some search strategies
        {
            //CalculateHF(int method) hF1=max{ei(m)}; h2=-dep(m)
            /*if (method==1)
				//h=max{ei(m)} where ei(m) is the sum of operation times of those remaining operation for all jobs
				//which are planned to be processed on the ith machine when the current system state is represented 
				//by the marking m
			{
				decimal[] ResourceTime={0,0,0};
				for(int n=0;n<MF.Length;++n)
				{
					if (MF[n]!=0)
						for(int x=0;x<ResourceTime.Length;++x)
							ResourceTime[x]=ResourceTime[x]+MF[n]*AStar.RST[n,x];
				}

				//加Mr
				if(MF[2]!=0 || MF[13]!=0)
					ResourceTime[0]=ResourceTime[0]+MF[2]*MrF[2]+MF[13]*MrF[13];
				if(MF[4]!=0 || MF[15]!=0)
					ResourceTime[1]=ResourceTime[1]+MF[4]*MrF[4]+MF[15]*MrF[15];
				if(MF[6]!=0 || MF[11]!=0)
					ResourceTime[2]=ResourceTime[2]+MF[6]*MrF[6]+MF[11]*MrF[11];

				decimal max=0;
				for(int c=0;c<ResourceTime.Length;++c)
					if(max<ResourceTime[c])
						max=ResourceTime[c];
				return max;

			}*/


            if (method == 2)
                return (-(FMarkingDepth + 1));

            return 0;
        }

        public virtual void FindEnabledTransitions()//寻找当前标识（FM[i]）下可实施的变迁，并对EnabledTransitions赋值（1：可以实施，0：不能实施）
        {//Find enabled transitions at a marking. It will assign values to EnabledTransitions such that 1 denotes the corresponding transition is enabled and 0 denotes not.
            int e;
            for (int j = 0; j < AStar.nt; ++j)
            {
                e = 1;
                for (int i = 0; i < AStar.np; ++i)
                {
                    if (AStar.LMINUS[i, j] != 0 && FM[i] < AStar.LMINUS[i, j]) //变迁可以实施的条件：当前输入库所的托肯数量大于变迁输入弧所需的输入托肯数量（ M(p) > I(p, t) ）
                    {
                        e = 0;
                        continue;
                    } 
                }
                EnabledTransitions[j] = e; //EnabledTransitions = new int[AStar.nt];
            }
        }

        public virtual void GetSuccessors(ArrayList ASuccessors, int hmethod, decimal ep2, decimal hValueStartNode) //获得当前节点的所有子节点，并添加到列表中
        {//Get the child nodes of the current node and handle them with OPEN and CLOSED. 
            //寻找当前标识下可实施的变迁
            FindEnabledTransitions();//Find the enabled transitions at the current node.
            for (int i = 0; i < FEnabledTransitions.Length; ++i)
            {
                if (FEnabledTransitions[i] == 1) //变迁可以实施 if the transition is enabled
                {
                    //程序选择哪个变迁取决于OPEN中相同f值的节点如何排队
                    
                    /*
                    for (int n = 0; n < AStar.np; ++n)//zzx
                    {
                        for (int m = 0; m < AStar.MAX_TOK_PA; ++m)
                        {
                            MrF[n, m] = FR[n, m];
                        }
                    }*/
                    //Calculate delt=max{R(pi,k-W(pi, tj)+1}; Because W(pi,tj)=1 in SC-nets, so delt=max{R(pi,k)} 
                    //where R(pi,k) denotes the remaining time of the last existing token in pi that is a pre-place of the transition selected to fire
                    delt = 0;
                    for (int x = 0; x < AStar.np; ++x)//zzx
                    {
                        if (AStar.LMINUS[x, i] > 0 && AStar.operationTimes[x]>0) // if it is an operation input place with time information
                        {
                            //注意，对于每个库所而言，R里面的托肯按照剩余时间非递增排序。且变迁从每个输入非资源库所需要的托肯数为1

                            if (delt < FR[x, FM[x] - 1])
                                delt = FR[x, FM[x] - 1];
                        }
                    }




                    //从变迁的输入库所中移去相应的托肯  Remove tokens from the pre-places of the transition
                    //M(k)+ = M(k)- - LMINUS*u(k) , M(k)+ 和M(k)- 分别表示托肯移走前后的系统标识
                    for (int n = 0; n < AStar.np; ++n)
                    {
                        if (AStar.LMINUS[n, i] > 0)
                            MZ[n] = FM[n] - AStar.LMINUS[n, i]; //MZ：标识状态M(k)+ //MZ: denotes M(k)+
                        else
                            MZ[n] = FM[n];

                    }

                    //向变迁的所有输出库所中添加相应托肯 Add tokens into the post-places of the transition
                    //M(k+1)- = M(k)+ + LPLUS*u(k)
                    for (int n = 0; n < AStar.np; ++n)
                    {
                        if (AStar.LPLUS[n, i] > 0)
                            MF[n] = MZ[n] + AStar.LPLUS[n, i];
                        else
                            MF[n] = MZ[n];
                    }





                    //在剩余处理时间向量Mr(即R)中逐个元素地减去delt，若值小于0则赋值为0   ZZX
                    //Subtract delt from each element of Mr. If the result is below 0, then set the element to 0. 
                    //计算 Mr(k)+z = Mr(k)-z - delt(k)z
                    for (int n = 0; n < AStar.np; ++n)
                    {
                        for (int m = 0; m < AStar.MAX_TOK_PA; ++m)
                        {
                            MrZ[n, m] = FR[n, m] - delt;
                            if (MrZ[n, m] < 0)
                                MrZ[n, m] = 0;
                        }
                    }

                    //向变迁的所有输出库所的R中开头位置加入新托肯的操作时间，其它托肯的剩余时间向后移动 
                    //Mr(k+1)-z = Mr(k)+z + t(k)z
                    for (int n = 0; n < AStar.np; ++n)
                    {
                        if (AStar.LPLUS[n, i] > 0 && AStar.operationTimes[n]>0)//if p_n is an operation output place of the transition t_i
                        {
                            //All token remaining times in R(p_n, .) move one step to the right
                            for (int j = AStar.MAX_TOK_PA  - 1; j > 0; --j)                   
                                    MrF[n, j] = MrZ[n, j - 1];

                            //Add the operation time of the place to the first entry of R(p_n,.).
                            MrF[n, 0] = AStar.operationTimes[n];
                        }
                        else
                        {
                            for (int j = 0; j < AStar.MAX_TOK_PA; ++j)
                                MrF[n, j] = MrZ[n, j];
                        }
                    }




                    decimal g = FgValue + delt;
                    decimal h = CalculateH(hmethod, ep2, hValueStartNode);
                    decimal f = (decimal)g + h;

                    decimal hF=CalculateHF(2);//计算子节点的hF,这里未关联参数！！
                    //CalculateHF(int method) 1=max{ei(m)}; 2=-dep(m)
                    

                    AStarNode NewNode = new AStarNode(this, GoalNode, g, h, f, MF, MrF, i, FMarkingDepth + 1, hF, delt);
                    //AStarNode(父节点, 目标节点, g值, h值, f值, 节点的标志, 该标识下所有库所的剩余处理时间, 产生本标识所实施的变迁, 标志的深度, 从父标识到变迁实施得到本标识所用时间)
                    ASuccessors.Add(NewNode);
                }

            }//for循环结束 the end of the for structure.

        }


        public virtual void PrintNodeInfo(int loop) //打印当前节点的信息  Print the info. of the current node
        {
            Console.Write("loop:{0}\tf:{1}\tg:{2}\th:{3}\ttFireFrom:{4}\tDepth:{5} ", loop, FfValue, FgValue, FhValue, FTFireFrom + 1, FMarkingDepth);
            

            Console.Write("tEnabled:");
            for (int n = 0; n < EnabledTransitions.Length; ++n)
            {
                if (EnabledTransitions[n] == 1)
                    Console.Write("{0} ", n + 1);
            }
            Console.Write("\tM:");
            for (int i = 0; i < FM.Length; ++i)//输出M中为1的palce
            {
                if (FM[i] == 1)
                    Console.Write("{0} ", i + 1);
                if (FM[i] > 1)
                    Console.Write("{0}({1})", i + 1, FM[i]);
            }
            Console.Write("\tR:");
            for (int n = 0; n < AStar.np; ++n)
                for (int m = 0; m < AStar.MAX_TOK_PA; ++m)
                {

                    if (FR[n, m] != 0)

                        Console.Write("[{0}，{1}]:{2} ", n + 1, m + 1, FR[n, m]);

                }
            Console.WriteLine();
        }

        #endregion

        #region Overridden Methods

        public override bool Equals(object obj)
        {
            return IsSameState((AStarNode)obj);
        }

        public override int GetHashCode()
        {
            return base.GetHashCode();
        }

        #endregion

        #region IComparable Members

        public int CompareTo(object obj)
        {
            return (fValue.CompareTo(((AStarNode)obj).fValue));
        }

        #endregion
    }

    public sealed class AStar //Petri网模型运行所需的全局属性和行为
    {
        #region Private Fields
        private AStarNode FStartNode;//起始节点 the start node of the search
        private AStarNode FGoalNode;//目标节点 the goal node
        private Heap FOpenList;//Open列表 the OPEN list
        private Heap FClosedList;//Close列表 the CLOSED list
        private ArrayList FSuccessors;//子节点列表 the list to contain the child nodes
        //private ArrayList FExpandedList;//已扩展节点列表 the list to contain expanded nodes
        private ArrayList FSolution;//结果方案列表 the list contains the nodes in the obtained schedule
        private int FNExpandedNode;//已扩展节点数 the number of expanded nodes
        #endregion

        #region Properties

        public static decimal[] operationTimes;//各库所的操作时间（资源库所操作时间为0） Operation times of places (for any resource place and idle place, it equals zero)

        public static int[,] LPLUS;//后置关联矩阵L+ The post-incidence matrix L+
        public static int[,] LMINUS;//前置关联矩阵L- The pre-incidence matrix L-

        public static int np;//Petri网中库所数(含资源)  The number of places in the net (including resource places)
        public static int nt;//Petri网中变迁数 The number of transitions in the net
        public static int nrs;//Petri网中资源库所数 The number of resource places

        public static int[] StartM;//开始节点的标识向量 The marking of the start node
        public static int[] GoalM;//目标节点的标识向量 The marking of the goal node
        public static decimal[,] StartMr;//开始节点的剩余处理时间矩阵 The token remaining time matrix of the start node
        public static decimal[,] GoalMr;//目标节点的剩余处理时间矩阵 The token remaining time matrix of the end node
        public static decimal[,] MrF;
        public static int MAX_TOK_PA; //活动库所的最大容量 The maximal number of tokens in any activity place. It will be set automatically by analyzing the input files.



        public ArrayList Solution//结果方案列表 A list containing the obtained schedule
        {
            get
            {
                return FSolution;
            }
        }
        public int NExpandedNode//已扩展节点数 The number of expanded nodes
        {
            get
            {
                return FNExpandedNode;
            }
            set
            {
                FNExpandedNode = value;
            }
        }



        //*********************************
        //Note that before h1 and h9 are used, some parameters of the tested Petri net should be given in CalculateH() in AStar.cs. 
        //If h7 is used, the number of resource places, the WRT matrix, the Upi matrix, and the M0r vector of the tested Petri net should be given in the class AStar.  //Revised when h7 is used!!
        //*********************************

        //private ArrayList ChildrenInOpenList = new ArrayList();//ArrayList 可动态增加的数组

         /*  
                  //===================================== start of xiong98 =====================================
                 ResNum = 3; //the number of resource places

                 WRT =
                 {
                             {2,3,4},{0,3,4},{0,3,4},{0,0,4},{0,0,4},{0,0,0},{0,0,0},
                             {2,2,4},{2,2,0},{2,2,0},{0,2,0},{0,2,0},{0,0,0},{0,0,0},
                             {3,3,5},{0,3,5},{0,3,5},{0,3,0},{0,3,0},{0,0,0},{0,0,0},
                             {3,3,4},{3,0,4},{3,0,4},{3,0,0},{3,0,0},{0,0,0},{0,0,0},
                             {0,0,0},{0,0,0},{0,0,0}
                         };
                     /*   double[,] WRT =
                     {
                   {2,1.5,4},{0,1.5,4},{0,1.5,4},{0,0,4},{0,0,4},{0,0,0},{0,0,0},
                   {2,1,4},{2,1,0},{2,1,0},{0,1,0},{0,1,0},{0,0,0},{0,0,0},
                   {3,1.5,5},{0,1.5,5},{0,1.5,5},{0,1.5,0},{0,1.5,0},{0,0,0},{0,0,0},
                   {3,1.5,4},{3,0,4},{3,0,4},{3,0,0},{3,0,0},{0,0,0},{0,0,0},
                   {0,0,0},{0,0,0},{0,0,0}
                           };*/
                //库所pi需要多少个资源r
                /*         decimal[,] Upi =
                          {
                             {0,0,0},{1,0,0},{0,0,0},{0,1,0},{0,0,0},{0,0,1},{0,0,0},
                             {0,0,0},{0,0,1},{0,0,0},{1,0,0},{0,0,0},{0,1,0},{0,0,0},
                             {0,0,0},{1,0,0},{0,0,0},{0,0,1},{0,0,0},{0,1,0},{0,0,0},
                             {0,0,0},{0,1,0},{0,0,0},{0,0,1},{0,0,0},{1,0,0},{0,0,0},
                             {0,0,0},{0,0,0},{0,0,0}
                         };
                         //手动计算资源库所的资源数量
                         int[] M0r = new int[ResNum] { 1, 1, 1 };
                         /*    for (int i = 0; i < ResourceTime.Length; ++i)
                             {
                                 M0r[i] = AStar.StartM[28 + i];
                                // Console.Write("[{0}]{1}",i,M0r[i]);
                               //  Console.WriteLine();
                             }*/

                //===================================== end of xiong98 =====================================

                
                



        /*
                 
                //===================================== start of ChenFig5 ===================================== 注意：后面还有ChenFig5_revised(with weighted arcs and multiple resource copies, for SMC2021)

                public const int ResNum = 6; //the number of resource places
                public static int[] M0r = new int[ResNum] { 1, 1, 1, 1, 1, 1 }; //the number of tokens in each resource place at the initial marking


       
                public static double[,] WRT = //The weighted remaining time matrix. Note that MRT only consider non-resource places.注意：如果使用decimal，则每个数值后要加m，所以此处使用double，具体计算时使用(decimal)进行类型转换
               {
                      {0,0,7,5,0,3},//p1   
                      {0,0,4,5,0,3},
                      {0,0,4,5,0,3},
                      {0,0,4,5,0,3},
                      {0,0,0,5,0,3},
                      {0,0,0,5,0,0},
                      {0,0,0,0,0,0},//p7
                      {4,3,9,2,0,0},//p8
                      {4,3,9,0,0,0},
                      {0,3,9,0,0,0},
                      {0,3,5,0,0,0},
                      {0,0,5,0,0,0},
                      {0,0,0,0,0,0},//p13
                      {0,0,0,0,0,0},//p20
                      {0,0,0,0,0,0}//p21
                };

                public static double[,] Upi = //各库所使用资源的矩阵；Note that Upi only consider non-resource places.注意：如果使用decimal，则每个数值后要加m，所以此处使用double，具体计算时使用(decimal)进行类型转换
                     {
                         {0,0,0,0,0,0,0},
                         {0,0,1,0,0,0,0},
                         {0,1,0,0,0,0,0},
                         {0,0,0,0,0,1,0},
                         {0,0,1,0,0,0,0},
                         {0,0,0,0,0,0,1},
                         {0,0,0,0,1,0,0},
                         {0,0,0,0,0,0,0},//p8
                         {0,0,0,0,1,0,0},
                         {1,0,0,0,0,0,0},
                         {0,0,1,0,0,0,0},
                         {0,1,0,0,0,0,0},
                         {0,0,1,0,0,0,0},//p13
                         {0,0,0,0,0,0,0},//p20
                         {0,0,0,0,0,0,0}//p21
                    };          
          
          //===================================== end of ChenFig5 =====================================
                    
        */

                   /*               
                   //===================================== start of ChenFig5_revised(with weighted arcs and multiple resource copies, for SMC2021) =====================================
                   public const int ResNum = 6; //资源库所数量；the number of resource places        

                   public static double[,] WRT = //The weighted remaining time matrix. Note that MRT only consider non-resource places.注意：如果使用decimal，则每个数值后要加m，所以此处使用double，具体计算时使用(decimal)进行类型转换
                   {
                      {0,0,3,0,3.5,5}, 
                      {0,0,3,0,2,5}, 
                      {0,0,3,0,2,5}, 
                      {0,0,3,0,2,5}, 
                      {0,0,3,0,0,5}, 
                      {0,0,0,0,0,5}, 
                      {0,0,0,0,0,0}, 
                      {0,3,0,4,6.5,2}, 
                      {0,3,0,4,6.5,0}, 
                      {0,3,0,0,6.5,0}, 
                      {0,3,0,0,2.5,0}, 
                      {0,0,0,0,2.5,0}, 
                      {0,0,0,0,0,0}, 
                      {0,0,0,0,0,0}, 
                      {0,0,0,0,0,0} 
                   };
                   public static double[,] Upi =  //各库所使用资源的矩阵；Note that Upi only consider non-resource places.注意：如果使用decimal，则每个数值后要加m，所以此处使用double，具体计算时使用(decimal)进行类型转换
                   {
                      {0,0,0,0,0,0},
                      {0,0,0,0,1,0},
                      {0,1,0,0,0,0},
                      {1,0,0,0,0,0},
                      {0,0,0,0,1,0},
                      {0,0,1,0,0,0},
                      {0,0,0,0,0,1},
                      {0,0,0,0,0,0},
                      {0,0,0,0,0,1},
                      {0,0,0,1,0,0},
                      {0,0,0,0,2,0},
                      {0,1,0,0,0,0},
                      {0,0,0,0,1,0},
                      {0,0,0,0,0,0},
                      {0,0,0,0,0,0} 
                   };

                   public static int[] M0r = new int[ResNum] { 1, 1, 1, 1, 2, 1 }; //各资源库所的初始托肯向量；the number of tokens in each resource place at the initial marking
                           
                   //===================================== end of ChenFig5_revised =====================================
                   */


        /*
        //===================================== start of ChenFig6 =====================================
        public const int ResNum = 7; //the number of resource places
        public static int[] M0r = new int[ResNum] { 1, 1, 1, 2, 2, 2, 2 };


        public static double[,] WRT = //Only consider non-resource places! Note that MRT only consider non-resource places.
                   {
                       {0,7,0,0,2,0,0},//p1
                       {0,5,0,0,2,0,0},
                       {0,5,0,0,0,0,0},
                       {0,0,0,0,0,0,0},
                       {3,3,4,0,0,0,0},//p5
                       {0,3,4,0,0,0,0},
                       {0,6,4,0,1,0,0},
                       {0,0,4,0,1,0,0},
                       {0,0,4,0,0,0,0},
                       {0,0,0,0,0,0,0},
                       {0,3,4,0,0,0,2},
                       {0,0,4,0,0,0,2},
                       {0,0,4,0,0,0,0},//p13
                       {2,4,6,0,0,3,1.5},//p14
                       {2,4,0,0,0,3,1.5},
                       {2,4,0,0,0,3,0},
                       {2,0,0,0,0,3,0},
                       {2,0,0,0,0,0,0},
                       {0,0,0,0,0,0,0},//p19
                       {0,0,0,0,0,0,0},//p27
                       {0,0,0,0,0,0,0},//p28
                       {0,0,0,0,0,0,0} //p29
                    };
        public static double[,] Upi = //Only consider non-resource places! 
                    {
                        {0,0,0,0,0,0,0},
                        {0,1,0,0,0,0,0},
                        {0,0,0,0,1,0,0},
                        {0,1,0,0,0,0,0},
                        {0,0,0,0,0,0,0},
                        {1,0,0,0,0,0,0},
                        {0,0,0,1,0,0,0},
                        {0,1,0,0,0,0,0},
                        {0,0,0,0,1,0,0},
                        {0,0,1,0,0,0,0},
                        {0,0,0,0,0,1,0},
                        {0,1,0,0,0,0,0},
                        {0,0,0,0,0,0,1},
                        {0,0,0,0,0,0,0},
                        {0,0,1,0,0,0,0},
                        {0,0,0,0,0,0,1},
                        {0,1,0,0,0,0,0},
                        {0,0,0,0,0,1,0},
                        {1,0,0,0,0,0,0},
                        {0,0,0,0,0,0,0},
                        {0,0,0,0,0,0,0},
                        {0,0,0,0,0,0,0}
                    };
        //===================================== end of ChenFig6 =====================================
         */
         

       /*
        //===================================== start of Chen2011Big =====================================
        public const int ResNum = 12; //the number of resource places
        public static int[] M0r = new int[ResNum] { 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2 };

        public static double[,] WRT = //Only consider non-resource places! Note that MRT only consider non-resource places. WRT即考虑资源拷贝数，也考虑弧权重
                   {
                       {5,0,2,0,0,0,0,0,0,0,0,0},//p1
                       {0,0,2,0,0,0,0,0,0,0,0,0},//p2
                       {0,4,2,0,0,0,3,0,0,0,0,0},//p3
                       {0,0,2,0,0,0,3,0,0,0,0,0},//p4
                       {0,0,2,0,0,0,0,0,0,0,0,0},//p5
                       {0,0,4,0,0,0,0,0,0.5,0,0,0},//p6
                       {0,0,2,0,0,0,0,0,0.5,0,0,0},//p7
                       {0,0,2,0,0,0,0,0,0,0,0,0},//p8
                       {0,0,0,0,0,0,0,0,0,0,0,0},//p9
                       {0,6,0,0,4,0,1,0,0,0,1,0},//p10
                       {0,3,0,0,4,0,1,0,0,0,1,0},//p11
                       {0,3,0,0,4,0,1,0,0,0,0,0},//p12
                       {0,0,0,0,4,0,1,0,0,0,0,0},//p13
                       {0,0,0,0,4,0,0,0,0,0,0,0},//p14
                       {0,0,0,0,0,0,0,0,0,0,0,0},//p15
                       {7,0,8,0,0,0,0,1,1,0,0,0},//p16
                       {0,0,0,0,0,0,0,0,0,0,0,0},//p17
                       {7,0,0,0,0,0,0,0,0,0,0,0},//p18
                       {7,0,0,0,0,0,0,1,0,0,0,0},//p19
                       {7,0,3,0,0,0,0,1,0,0,0,0},//p20
                       {7,0,3,0,0,0,0,1,1,0,0,0},//p21
                       {0,2,0,5,0,0,0,0,0,0,0,0},//p22
                       {0,2,0,0,0,0,0,0,0,0,0,0},//p23
                       {0,6,0,0,0,0,0,0,0,0.5,0,0},//p24
                       {0,2,0,0,0,0,0,0,0,0.5,0,0},//p25
                       {0,2,0,0,0,0,0,0,0,0,0,0},//p26
                       {0,2,4,0,0,0,1.5,0,0,0,0,0},//p27
                       {0,2,0,0,0,0,1.5,0,0,0,0,0},//p28
                       {0,2,0,0,0,0,0,0,0,0,0,0},//p29
                       {0,0,0,0,0,0,0,0,0,0,0,0},//p30
                       {10,0,0,0,6,0.5,0,0,0,0,0,1.5},//p31
                       {10,0,0,0,0,0.5,0,0,0,0,0,1.5},//p32
                       {10,0,0,0,0,0.5,0,0,0,0,0,0},//p33
                       {7,0,0,0,0,0.5,0,0,0,0,0,0},//p34
                       {7,0,0,0,0,0,0,0,0,0,0,0},//p35
                       {0,0,0,0,0,0,0,0,0,0,0,0},//p36
                       {0,0,0,0,0,0,0,0,0,0,0,0},//p49
                       {0,0,0,0,0,0,0,0,0,0,0,0},//p50
                       {0,0,0,0,0,0,0,0,0,0,0,0},//p51
                       {0,0,0,0,0,0,0,0,0,0,0,0},//p52
                       {0,0,0,0,0,0,0,0,0,0,0,0} //p53
                    };
        public static double[,] Upi = //Only consider non-resource places! 用于算h_H的尾巴，即weighted token remaining time
                    {
					   {0,0,0,0,0,0,0,0,0,0,0,0},//p1
                       {1,0,0,0,0,0,0,0,0,0,0,0},//p2
                       {0,0,0,0,0,1,0,0,0,0,0,0},//p3
                       {0,1,0,0,0,0,0,0,0,0,0,0},//p4
                       {0,0,0,0,0,0,1,0,0,0,0,0},//p5
                       {0,0,0,0,0,0,0,1,0,0,0,0},//p6
                       {0,0,1,0,0,0,0,0,0,0,0,0},//p7
                       {0,0,0,0,0,0,0,0,1,0,0,0},//p8
                       {0,0,1,0,0,0,0,0,0,0,0,0},//p9
                       {0,0,0,0,0,0,0,0,0,0,0,0},//p10
                       {0,1,0,0,0,0,0,0,0,0,0,0},//p11
                       {0,0,0,0,0,0,0,0,0,0,1,0},//p12
                       {0,1,0,0,0,0,0,0,0,0,0,0},//p13
                       {0,0,0,0,0,0,1,0,0,0,0,0},//p14
                       {0,0,0,0,1,0,0,0,0,0,0,0},//p15
                       {0,0,0,0,0,0,0,0,0,0,0,0},//p16
                       {1,0,0,0,0,0,0,0,0,0,0,0},//p17
                       {0,0,0,0,0,0,0,1,0,0,0,0},//p18
                       {0,0,1,0,0,0,0,0,0,0,0,0},//p19
                       {0,0,0,0,0,0,0,0,1,0,0,0},//p20
                       {0,0,1,0,0,0,0,0,0,0,0,0},//p21
                       {0,0,0,0,0,0,0,0,0,0,0,0},//p22
                       {0,0,0,1,0,0,0,0,0,0,0,0},//p23
                       {0,0,0,0,0,0,0,0,0,0,1,0},//p24
                       {0,1,0,0,0,0,0,0,0,0,0,0},//p25
                       {0,0,0,0,0,0,0,0,0,1,0,0},//p26
                       {0,0,0,0,0,0,0,0,1,0,0,0},//p27
                       {0,0,1,0,0,0,0,0,0,0,0,0},//p28
                       {0,0,0,0,0,0,1,0,0,0,0,0},//p29
                       {0,1,0,0,0,0,0,0,0,0,0,0},//p30
                       {0,0,0,0,0,0,0,0,0,0,0,0},//p31
                       {0,0,0,0,1,0,0,0,0,0,0,0},//p32
                       {0,0,0,0,0,0,0,0,0,0,0,1},//p33
                       {1,0,0,0,0,0,0,0,0,0,0,0},//p34
                       {0,0,0,0,0,1,0,0,0,0,0,0},//p35
                       {1,0,0,0,0,0,0,0,0,0,0,0},//p36
                       {0,0,0,0,0,0,0,0,0,0,0,0},//p49
                       {0,0,0,0,0,0,0,0,0,0,0,0},//p50
                       {0,0,0,0,0,0,0,0,0,0,0,0},//p51
                       {0,0,0,0,0,0,0,0,0,0,0,0},//p52
                       {0,0,0,0,0,0,0,0,0,0,0,0} //p53
                    };

        //===================================== end of Chen2011Big =====================================
        */

        /*
           //===================================== start of New4x3 =====================================
           const int ResNum = 3; //the number of resource places


           double[,] WRT =
           {
               {5,4,4},{0,4,4},{0,4,4},{0,0,4},{0,0,4},{0,0,0},{0,0,0},
               {2,2,5},{2,0,5},{2,0,5},{2,0,0},{2,0,0},{0,0,0},{0,0,0},
               {2,5,5},{2,5,0},{2,5,0},{0,5,0},{0,5,0},{0,0,0},{0,0,0},
               {2,4,2},{2,4,0},{2,4,0},{2,0,0},{2,0,0},{0,0,0},{0,0,0},
               {0,0,0},{0,0,0},{0,0,0}
           };
          decimal[,] Upi =
          {
              {0,0,0},{1,0,0},{0,0,0},{0,1,0},{0,0,0},{0,0,1},{0,0,0},
              {0,0,0},{0,1,0},{0,0,0},{0,0,1},{0,0,0},{1,0,0},{0,0,0},
              {0,0,0},{0,0,1},{0,0,0},{1,0,0},{0,0,0},{0,1,0},{0,0,0},
              {0,0,0},{0,0,1},{0,0,0},{0,1,0},{0,0,0},{1,0,0},{0,0,0},
              {0,0,0},{0,0,0},{0,0,0},
          };

           int[] M0r = new int[ResNum] { 1, 1, 1};
           //===================================== end of New4x3 =====================================
           */


        /*
       //===================================== start of Huang2012Fig1 =====================================
       public const int ResNum = 3; //the number of resource places
       public static int[] M0r = new int[ResNum] {1, 1, 1};

       public static double[,] WRT = { //Only consider non-resource places! Note that MRT only consider non-resource places. WRT即考虑资源拷贝数，也考虑弧权重;用前检查
                                    {57,0,42.5},    //p1	
                                    {57,0,42.5},    //p2  
                                    {57,0,42.5},    //p3  
                                    {57,0,42.5},    //p4  
                                    {57,0,0},       //p5  
                                    {57,0,0},       //p6  
                                    {0,0,0},        //p7  
                                    {0,0,25.5},       //p8  
                                    {0,0,25.5},       //p9  
                                    {0,0,0},        //p10 
                                    {0,0,0},        //p11 
                                    {0,95,0},       //p12 
                                    {0,0,0},        //p13 
                                    {0,0,0},        //p14 
                                    {0,0,0},        //p15 
                                    {0,0,0},        //p16 
                                    {0,0,0},        //p17 
                                    {0,0,0},        //p18 
                                    {0,0,0},        //p19 
                                    {0,0,0},        //p20 
                                    {0,78,37.5},    //p21 
                                    {0,0,37.5},     //p22 
                                    {0,0,37.5},     //p23 
                                    {0,0,0},        //p24 
                                    {0,0,0},        //p25 
                                    {0,0,0},        //p26 
                                    {0,70,0},       //p27 
                                    {0,70,0},       //p28 
                                    {0,0,0},        //p29 
                                    {0,0,0},        //p30 
                                    {93,0,87.5},    //p31 
                                    {93,0,38},      //p32 
                                    {93,0,38},      //p33 
                                    {93,0,0},       //p34 
                                    {93,0,0},       //p35 
                                    {0,0,0},        //p36 
                                    {0,0,0}         //p37 
                               };
         
       public static decimal[,] Upi = { //Only consider non-resource places! 用于算h_H的尾巴，即weighted token remaining time;用前检查
                                    {0,0,0}, //p1	
                                    {0,0,1}, //p2 
                                    {0,1,0}, //p3 
                                    {0,0,0}, //p4 
                                    {0,0,1}, //p5 
                                    {0,0,0}, //p6 
                                    {1,0,0}, //p7 
                                    {1,0,0}, //p8 
                                    {0,0,0}, //p9 
                                    {0,0,1}, //p10
                                    {0,0,0}, //p11
                                    {0,0,0}, //p12
                                    {0,1,0}, //p13
                                    {0,0,0}, //p14
                                    {0,1,0}, //p15
                                    {0,0,1}, //p16
                                    {0,0,0}, //p17
                                    {1,0,0}, //p18
                                    {0,0,1}, //p19
                                    {0,0,0}, //p20
                                    {0,0,0}, //p21
                                    {0,1,0}, //p22
                                    {0,0,0}, //p23
                                    {0,0,1}, //p24
                                    {0,0,0}, //p25
                                    {1,0,0}, //p26
                                    {0,0,1}, //p27
                                    {0,0,0}, //p28
                                    {0,1,0}, //p29
                                    {0,0,0}, //p30
                                    {0,0,0}, //p31
                                    {0,0,1}, //p32
                                    {0,0,0}, //p33
                                    {0,0,1}, //p34
                                    {0,0,0}, //p35
                                    {1,0,0}, //p36
                                    {0,0,0}  //p37
                                }; 
     
       //===================================== start of Huang2012Fig1 =====================================
        */



        //===================================== start of Huang2012Fig1Reviesed (即MyTASE2022Fig2Generalized)=====================================       
               public const int ResNum = 3; //the number of resource places           
               public static int[] M0r = new int[ResNum] { 1, 1, 2 };


               public static double[,] WRT = { //Only consider non-resource places! Note that MRT only consider non-resource places. WRT即考虑资源拷贝数，也考虑弧权重
                                    {57,0,42.5},    //p1	
                                    {57,0,42.5},    //p2  
                                    {57,0,42.5},    //p3  
                                    {57,0,42.5},    //p4  
                                    {57,0,0},       //p5  
                                    {57,0,0},       //p6  
                                    {0,0,0},        //p7  
                                    {0,0,51},       //p8  
                                    {0,0,51},       //p9  
                                    {0,0,0},        //p10 
                                    {0,0,0},        //p11 
                                    {0,95,0},       //p12 
                                    {0,0,0},        //p13 
                                    {0,0,0},        //p14 
                                    {0,0,0},        //p15 
                                    {0,0,0},        //p16 
                                    {0,0,0},        //p17 
                                    {0,0,0},        //p18 
                                    {0,0,0},        //p19 
                                    {0,0,0},        //p20 
                                    {0,78,37.5},    //p21 
                                    {0,0,37.5},     //p22 
                                    {0,0,37.5},     //p23 
                                    {0,0,0},        //p24 
                                    {0,0,0},        //p25 
                                    {0,0,0},        //p26 
                                    {0,70,0},       //p27 
                                    {0,70,0},       //p28 
                                    {0,0,0},        //p29 
                                    {0,0,0},        //p30 
                                    {93,0,87.5},    //p31 
                                    {93,0,38},      //p32 
                                    {93,0,38},      //p33 
                                    {93,0,0},       //p34 
                                    {93,0,0},       //p35 
                                    {0,0,0},        //p36 
                                    {0,0,0}         //p37 
                               };

               public static decimal[,] Upi = { //Only consider non-resource places! 用于算h_H的尾巴，即weighted token remaining time
                                    {0,0,0}, //p1	
                                    {0,0,1}, //p2 
                                    {0,1,0}, //p3 
                                    {0,0,0}, //p4 
                                    {0,0,1}, //p5 
                                    {0,0,0}, //p6 
                                    {1,0,0}, //p7 
                                    {1,0,0}, //p8 
                                    {0,0,0}, //p9 
                                    {0,0,2}, //p10
                                    {0,0,0}, //p11
                                    {0,0,0}, //p12
                                    {0,1,0}, //p13
                                    {0,0,0}, //p14
                                    {0,1,0}, //p15
                                    {0,0,1}, //p16
                                    {0,0,0}, //p17
                                    {1,0,0}, //p18
                                    {0,0,1}, //p19
                                    {0,0,0}, //p20
                                    {0,0,0}, //p21
                                    {0,1,0}, //p22
                                    {0,0,0}, //p23
                                    {0,0,1}, //p24
                                    {0,0,0}, //p25
                                    {1,0,0}, //p26
                                    {0,0,1}, //p27
                                    {0,0,0}, //p28
                                    {0,1,0}, //p29
                                    {0,0,0}, //p30
                                    {0,0,0}, //p31
                                    {0,0,1}, //p32
                                    {0,0,0}, //p33
                                    {0,0,1}, //p34
                                    {0,0,0}, //p35
                                    {1,0,0}, //p36
                                    {0,0,0}  //p37
                                };

               //===================================== start of Huang2012Fig1Reviesed (即MyTASE2022Fig2Generalized)=====================================       


        #endregion

        #region Constructors

        public AStar(string initfile, string matrixfile)//构造函数
        {
            FOpenList = new Heap();
            FClosedList = new Heap();
            FSuccessors = new ArrayList();
            FSolution = new ArrayList();
            //FExpandedList = new ArrayList();

            Read_initfile(initfile);
            Read_matrixfile(matrixfile);



            Console.WriteLine("Petri网中库所数(含资源) The number of places (including resource places)：" + np);
            Console.WriteLine("Petri网中变迁数 The number of transitions：" + nt);
            Console.WriteLine("Petri网中资源库所数 The number of resource places：" + nrs);
            Console.WriteLine("初始标识 The initial marking：");

            for (int i = 0; i < np; i++)
            {
                Console.Write(StartM[i] + " ");
            }
            Console.WriteLine();
            Console.WriteLine("操作的时间 Operation times：");
            for (int i = 0; i < np; i++)
            {
                Console.Write(operationTimes[i] + " ");
            }
            Console.WriteLine();
            Console.WriteLine("目标标识 The goal marking：");
            for (int i = 0; i < np; i++)
            {
                Console.Write(GoalM[i] + " ");
            }
            Console.WriteLine();
            Console.WriteLine("后置伴随矩阵 The post-incidence matrix L+：");
            for (int i = 0; i < np; ++i)
            {
                for (int j = 0; j < nt; ++j)
                {
                    Console.Write(LPLUS[i, j] + " ");
                }
                Console.WriteLine();
            }
            Console.WriteLine();
            Console.WriteLine("前置伴随矩阵 The pre-incidence matrix L-：");
            for (int i = 0; i < np; ++i)
            {
                for (int j = 0; j < nt; ++j)
                {
                    Console.Write(LMINUS[i, j] + " ");
                }
                Console.WriteLine();
            }
            Console.WriteLine();


            StartMr = new decimal[np, AStar.MAX_TOK_PA];
            GoalMr = new decimal[np, AStar.MAX_TOK_PA];
            for (int i = 0; i < np; ++i)
                for (int j = 0; j < AStar.MAX_TOK_PA; ++j)
                {
                    StartMr[i, j] = 0;
                    GoalMr[i, j] = 0;
                }

        }

        #endregion

        #region Private Methods

        private static void Read_initfile(string filename)
        {
            StreamReader SR;
            try
            {
                SR = File.OpenText(filename);
            }
            catch
            {
                Console.Write(filename + " open failed!");
                return;
            }
            string S;
            string[] SubS;

            //init文件的第一行  The first line of the init.txt
            {
                S = SR.ReadLine();

                S = S.Trim();
                while (S == "")
                {
                    S = SR.ReadLine();
                    S = S.Trim();
                }

                SubS = System.Text.RegularExpressions.Regex.Split(S, @"\s{1,}"); //以一个或多空格为分隔
                
                //SubS = S.Split(new char[] {' '});//string[]不指定大小就可以使用

                //Petri网中库所数(含资源)
                np = SubS.Length;

                //初始marking
                StartM = new int[np];
                for (int i = 0; i < SubS.Length; ++i)
                {
                    StartM[i] = Convert.ToInt32(SubS[i]);
                }
            }


            //init文件的第二行 The second line of the init.txt
            {
                S = SR.ReadLine(); //ReadLine可能返回空行

                S = S.Trim();
                while (S == "")
                {
                    S = SR.ReadLine();
                    S = S.Trim();
                }
               
                SubS = System.Text.RegularExpressions.Regex.Split(S, @"\s{1,}"); //以一个或多空格为分隔


                operationTimes = new decimal[np]; //各库所的操作时间
                for (int i = 0; i < SubS.Length; ++i)                    
                        operationTimes[i] = Convert.ToInt32(SubS[i]);                      
                    
            }

            //init文件的第三行 the third line of the init.txt
            {
                S = SR.ReadLine(); //ReadLine可能返回空行
                S = S.Trim();
                while (S == "")
                {
                    S = SR.ReadLine();
                    S = S.Trim();
                }      

                SubS = System.Text.RegularExpressions.Regex.Split(S, @"\s{1,}"); //以一个或多空格为分隔

                //目标marking
                GoalM = new int[np];
                for (int i = 0; i < SubS.Length; ++i)
                {
                    GoalM[i] = Convert.ToInt32(SubS[i]);
                }
            }

            //Petri网中资源库所数 the number of resource places in the net
            nrs = 0;
            MAX_TOK_PA = 0;            
            for (int i = 0; i < SubS.Length; ++i)
            {
                if (StartM[i] != 0)
                {
                    if (StartM[i] == GoalM[i]) //在读取PN输入文件时自动计算资源库所最大容量，并统计资源数; MAX_TOK_PA will be set automatically by analyzing the input files.
                    {
                        nrs++;
                        if (MAX_TOK_PA < StartM[i])
                            MAX_TOK_PA = StartM[i];
                    }
                }

            }
            SR.Close();

            return;
        }

        private static void Read_matrixfile(string filename)
        {
            StreamReader SR;
            try
            {
                SR = File.OpenText(filename);
            }
            catch
            {
                Console.Write(filename + " open failed!");
                return;
            }


            string S;

            //Petri网中变迁数 the number of transitions in the net
            nt = 0;
            S = SR.ReadLine();
            while (S != null)
            {
                S = S.Trim();

                if (S != "") //S有时会是空格
                    ++nt;
                S = SR.ReadLine();
            }
            SR.Close();




            StreamReader SRR;
            try
            {
                SRR = File.OpenText(filename);
            }
            catch
            {
                Console.Write(filename + " open failed!");
                return;
            }

            //临时矩阵 nt * np
            int[,] temp = new int[nt, np];
            string[] SubS;
            int n = 0;

            S = SRR.ReadLine();            

            while (S != null)
            {
                S = S.Trim(); //去头尾空格
                if (S != "")
                {
                    //SubS = S.Split(new char[] { ' ' });
                    SubS = System.Text.RegularExpressions.Regex.Split(S, @"\s{1,}"); //以一个或多空格为分隔

                    for (int j = 0; j < np; ++j)        
                        temp[n, j] = Convert.ToInt32(SubS[j]);
                    n++;
                }               
                                
                S = SRR.ReadLine();
            }

            SRR.Close();

            //伴随矩阵L+
            LPLUS = new int[np, nt];

            //伴随矩阵L-
            LMINUS = new int[np, nt];

            for (int i = 0; i < nt; ++i)
            {
                for (int j = 0; j < np; ++j)
                {
                    if (temp[i, j] >= 1)
                        LPLUS[j, i] = temp[i, j];                    
                    else                    
                        LPLUS[j, i] = 0;
                    

                    if (temp[i, j] <= -1)
                        LMINUS[j, i] = -temp[i, j];    
                    else                    
                        LMINUS[j, i] = 0;                    
                }
            }
            
            return;
        }

        // HList按FfValue排好序了，将Node插入相同FfValue的第一个位置
        private int SortAdd(Heap HList, AStarNode Node)//将节点插入到相同FfValue值的第一个位置
        //Insert a node into HList as the first element of the nodes with same FfValue. 
        //The nodes in HList are ranked in a non-decreasing order of f-values. 
        {
            int position = 0;
            for (int i = 0; i < HList.Count; ++i)
            {
                AStarNode LNode = (AStarNode)HList[i];
                if (LNode.fValue >= Node.fValue)
                    break;
                else
                    ++position;
            }
            if (position == HList.Count)
                HList.Add(Node);//加到末尾处
            else
                HList.Insert(position, Node);
            return position;
        }

        private void PrintNodeList(object ANodeList)//输出某列表中所有节点的信息  Print the info. of all nodes in a given list. 
        {
            Console.WriteLine("\nNode list:");
            int i = 0;
            foreach (AStarNode n in (ANodeList as IEnumerable))
            {
                Console.Write("{0})\t", i + 1);
                i++;
                n.PrintNodeInfo(0);
            }
            Console.WriteLine("=============================================================");
        }

        #endregion

        #region Public Methods

        public void PrintNumberOfOpenNodes()//用于向屏幕输出open节点数  //output the number of nodes in OPEN to your screen.
        {
            Console.WriteLine("The number of nodes in OPEN: {0}", FOpenList.Count);
        }

        //向输出文件result.txt中加入最终运行时间和扩展节点数
        public void PrintTimeExpandedNodes(TimeSpan elapsedTimeTotal, int NExpandedNode, string fileNameOutput)
        {
            FileStream ostrm;
            StreamWriter writer;
            TextWriter oldOut = Console.Out;

            try
            {
                ostrm = new FileStream(fileNameOutput, FileMode.Append, FileAccess.Write);
                writer = new StreamWriter(ostrm);
            }
            catch (Exception err)
            {
                Console.WriteLine(err.Message);
                Console.WriteLine("Cannot open " + fileNameOutput + " to write results!");
                return;
            }
            Console.SetOut(writer);

            Console.WriteLine("===============================================================");            
            Console.WriteLine("Total time：{0} seconds : {1} milliseconds   (i.e., hours={2}, minutes={3}, seconds={4}, milliseconds={5})", elapsedTimeTotal.Hours * 3600 + elapsedTimeTotal.Minutes * 60 + elapsedTimeTotal.Seconds, elapsedTimeTotal.Milliseconds, elapsedTimeTotal.Hours, elapsedTimeTotal.Minutes, elapsedTimeTotal.Seconds, elapsedTimeTotal.Milliseconds);
            Console.WriteLine("Total expanded markings #:{0}", NExpandedNode);

            Console.SetOut(oldOut);
            writer.Close();
            ostrm.Close();
        }
        

        //向屏幕输出，并写文件result.txt  //Output the results to your screen and a file result.txt. filemode=0表示以create方式创建和输出文件；否则以append方式输出文件
        public void PrintSolution(int filemode, string filename, int hmethod, int opensize, int hFmethod, decimal ep, decimal ep2, TimeSpan elapsedTimeRunI, TimeSpan elapsedTimeTotal, int runCount, decimal makespan, int NExpandedNodeRunI, int NExpandedNode, string fileNameOutput) 
        {            
            Console.WriteLine("************* The obtained schedule： ***********");
            PrintNodeList(FSolution);//向屏幕输出FSolution	//Output the obtained schedule to the screen		
            Console.WriteLine("The number of expanded markings:{0}", NExpandedNode);

            
            FileStream ostrm;
            StreamWriter writer;
            TextWriter oldOut = Console.Out;

            
            try
            {
                if (filemode == 0)
                    ostrm = new FileStream(fileNameOutput, FileMode.Create, FileAccess.Write);
                else
                    ostrm = new FileStream(fileNameOutput, FileMode.Append, FileAccess.Write);
                writer = new StreamWriter(ostrm);
            }
            catch (Exception err)
            {
                Console.WriteLine(err.Message);
                Console.WriteLine("Cannot open " + fileNameOutput + " for writing results!");
                return;
            }
            Console.SetOut(writer);

            Console.WriteLine("=====================Start of a run# {0}=======================", runCount);
            DateTime nowTime = DateTime.Now;
            Console.WriteLine("{0}", nowTime.ToString());
            Console.WriteLine("Petri net={0}, h={1}, Open size={2}, h2={3}", filename, hmethod, opensize, hFmethod);
            Console.WriteLine("ep(for A^*_ep)={0}, ep2(for h dynamic weighting)={1}", ep, ep2);
            Console.WriteLine("---------------------------------------------------------------");
            Console.WriteLine("Run #:{0}", runCount);
            Console.WriteLine("Makespan:{0}", makespan);
            Console.WriteLine("Newly expanded markings #:{0}", NExpandedNodeRunI);
            Console.WriteLine("Total expanded markings #:{0}", NExpandedNode);
            Console.WriteLine("This run time：{0} seconds : {1} milliseconds   (i.e., hours={2}, minutes={3}, seconds={4}, milliseconds={5})", elapsedTimeRunI.Hours * 3600 + elapsedTimeRunI.Minutes * 60 + elapsedTimeRunI.Seconds, elapsedTimeRunI.Milliseconds, elapsedTimeRunI.Hours, elapsedTimeRunI.Minutes, elapsedTimeRunI.Seconds, elapsedTimeRunI.Milliseconds);
            Console.WriteLine("Total time：{0} seconds : {1} milliseconds   (i.e., hours={2}, minutes={3}, seconds={4}, milliseconds={5})", elapsedTimeTotal.Hours * 3600 + elapsedTimeTotal.Minutes * 60 + elapsedTimeTotal.Seconds, elapsedTimeTotal.Milliseconds, elapsedTimeTotal.Hours, elapsedTimeTotal.Minutes, elapsedTimeTotal.Seconds, elapsedTimeTotal.Milliseconds);    
            Console.WriteLine("===============================================================");

            Console.WriteLine("************* The best schedule found so far： ***********");
            PrintNodeList(FSolution);//向文件输出FSolution	//output FSolution to result.txt.


            /*
            Console.WriteLine("************* FExpandedList ***********");
            Console.WriteLine("The number of expanded markings:{0}", NExpandedNode);
            PrintNodeList(FExpandedList);//向文件输出FExpandedList

            Console.WriteLine("************* OpenList ***********");
            PrintNodeList(FOpenList);//向文件输出FOpenList
            */

            
            Console.WriteLine("=======================End of a run==========================");
            Console.WriteLine();
            Console.WriteLine();
            Console.WriteLine();
            Console.WriteLine();
            


            Console.SetOut(oldOut);
            writer.Close();
            ostrm.Close();
            Console.WriteLine("Results have been written into " + fileNameOutput + "!");

        }





        public void FindPath_AnytimeAstar(AStarNode AStartNode, AStarNode AGoalNode, decimal ep, decimal ep2, int hmethod, int hFmethod, int opensize, bool printScreen, string filename)
        {
            //Note that before h1 and h9 are used, some parameters of the tested Petri net should be given in CalculateH() in AStar.cs. 
            //If h7 is used, the number of resource places, the WRT matrix, the Upi matrix, and the M0r vector of the tested Petri net should be given in FindPath() in AStar.cs.

            //hmethod:所用启发函数h  //hmethod: the used heuristic function:
            //h1=max{ei(m)} plus R; max{ei(m)} comes from Xiong98.
            //h2=0;
            //h4=-dep(m);
            //h7 = h_H=max{E[M(p_i)*WRT(pi,r)+ER(pi,x)*Upi(r)/M0(r)]} comes from Chapter 9 of our book and our pape: Bo Huang, et al. Scheduling Robotic Cellular Manufacturing Systems with Timed Petri Net, A* Search and Admissible Heuristic Function. IEEE Transactions on Automation Science and Engineering, Jan. 2022, 19(1): 243-250.;  
            //Before h7=h_H is used, the number of resource places, the WRT matrix, the Upi matrix, and the M0r vector of the Petri net should be given in the class AStar.
            //h9=hs+max{ei(m)}+he in which max{ei(m)} comes from Xiong98, hs denotes the necessary time before the resource is used, and he denotes the necessary time after the resource is used.


            //printScreen:是否向屏幕打印每个扩展节点的信息 //printScreen: whether or not to output every expanded node to your screen
            //ep: the parameter epsilon used in Chapter 9 in our book.
            //ep<0时表示没有ep的情况  ep<0 indicates the A* search does not use the epsilon. 
            //ep=0时，选OPEN中具有相同最小f值marking中有最小hFCost的(0比-1好)
            //ep>0时选择范围更大,选OPEN中具有不大于最小f值1+ep倍的marking中有最小hFCost的
            //ep>=0 indicates the A* search picks out the node with the minimal hFCost value for expansion among the nodes having the f-value between f_min and f_min*(1+ep) in OPEN.
            //opensize: the maximal number of nodes in OPEN. 
            //opensize=0 denotes unlimited. opensize>0 denotes the A* search will use the BF locally and BT globally as described in Chapter 10 of our book.

            //ep2: It is only for dynamic weighted search, i.e., h710=h+ep2*(1-dn/dG)*h. pe2s={0m},0表示无意义，无循环
            

            //1=h;2=-(FMarkingDepth+1);10=h;
            //从小到大排序

            FStartNode = AStartNode;
            FGoalNode = AGoalNode;

            FOpenList.Clear();
            FClosedList.Clear();
            FSuccessors.Clear();
            FSolution.Clear();
            //FExpandedList.Clear();
            NExpandedNode = 0;

            int NExpandedNodeRunI=0; //the number of newly expanded nodes in the ith run


            byte runCount = 1;  //计算当前最优结果的次数

            

            int loop = 0; //重要，用于调试定位

                       

            DateTime startTimeTotal; //总的搜索开始时间  the start time of the entire anytime A* search
            DateTime startTimeRunI; //本次计算当前最佳结果开始时间  the start time of the ith run 
            DateTime currentTime;
            TimeSpan elapsedTimeRunI;//本轮循环运行时间 the running time of find a best solution
            TimeSpan elapsedTimeTotal;//总运行时间 the total running time
            startTimeTotal = startTimeRunI = DateTime.Now;

            string[] fileNameOutput = new string[] { "0result-AWA-" + ep + "-" + filename + ".txt" }; //输出文件名，放在0result文件夹下

            FOpenList.Add(FStartNode);//将初始标识放入OPEN表中  Put the initial marking into OPEN.

            //计算起始节点S0的h值  Calculate the h-value of the start node (f-value=h-value for the start node)
            decimal hValueStartNode = 0;

            if (hmethod == 7)
            {
                decimal[] ResourceTime = new decimal[ResNum];
                for (byte i = 0; i < ResourceTime.Length; ++i)
                {
                    ResourceTime[i] = 0;
                }

                //计算起始节点S0的h值(即起始节点的f值,因为其g值为0)，hValueStartNode用于h12(IDW)=h(M)+ep *h(M),h(M)=h1;时计算M子节点的h!!!!!!!!!!!!!!!!!!!!!!
                for (byte n = 0; n < AStar.np - AStar.nrs; ++n)//除资源外的place数
                {
                    if (FStartNode.M[n] != 0)
                        for (byte x = 0; x < ResourceTime.Length; ++x)
                        {
                            ResourceTime[x] += FStartNode.M[n] * (decimal)AStar.WRT[n, x];
                        }
                }

                decimal max = 0;
                for (byte c = 0; c < ResourceTime.Length; ++c)
                    if (max < ResourceTime[c])
                        max = ResourceTime[c];
                hValueStartNode = max;
            }

            int infinity = 1000000;

            decimal f_upper = infinity; //an upper bound of the minimal cost of a path
            


            while (FOpenList.Count > 0)
            {
                loop++;

                /*
                if (loop == 9532)//for Debug
                {
                    loop++;
                    loop--;
                }*/

                AStarNode NodeCurrent;

                if (ep < 0)
                    NodeCurrent = (AStarNode)FOpenList.Pop();
                else //ep>=0,选OPEN中具有不大于最小f值1+ep倍的marking中有最小hFCost的
                {

                    int i = 0;                    
                    AStarNode N = (AStarNode)FOpenList[i];
                    decimal minF = N.fValue; //the minimal f-value in OPEN
                    decimal currentDeepestDepth = N.MarkingDepth; //the currently found deepest depth
                    int index = i;
              

                    while (i < FOpenList.Count - 1 && N.fValue <= (decimal)(1 + ep) * minF)
                    {
                        //FFOCALList.Add(N);
                        if (currentDeepestDepth < N.MarkingDepth)//Depth is the number of transition firings
                        {
                            currentDeepestDepth = N.MarkingDepth;
                            index = i;
                        }

                        i++;
                        N = (AStarNode)FOpenList[i];
                    }



                    NodeCurrent = (AStarNode)FOpenList[index];
                    FOpenList.Remove(FOpenList[index]);	//已经将要扩展的节点移走了



                }//else
                




                if (NodeCurrent.fValue < f_upper) //using the upper bound f_upper to prune some states                {
                {
                    //如果当前节点是目的节点，则回溯构造出当前最佳路径  If the current node equals the goal node, construct the current best schedule from the goal node back to the initial node.
                    if (NodeCurrent.IsGoal())
                    {
                        f_upper = NodeCurrent.fValue;
                        

                        FSolution.Clear();

                        while (NodeCurrent != null)
                        {
                            FSolution.Insert(0, NodeCurrent);
                            NodeCurrent = NodeCurrent.Parent;
                        }
                        
                        //打印当前最佳结果
                        currentTime = DateTime.Now;
                        elapsedTimeRunI = new TimeSpan(currentTime.Ticks - startTimeRunI.Ticks);//本轮循环运行时间 the running time of find a best solution
                        elapsedTimeTotal = new TimeSpan(currentTime.Ticks - startTimeTotal.Ticks);//总运行时间 the total running time

                        //NExpandedNodeRunI = NExpandedNode - NExpandedNodeRunI;

                        
                        
                        if (runCount == 1)
                            PrintSolution(0, filename, hmethod, opensize, hFmethod, ep, ep2, elapsedTimeRunI, elapsedTimeTotal, runCount, f_upper, NExpandedNodeRunI, NExpandedNode, fileNameOutput[0]);
                            //向屏幕和文件输出结果	Output results to your screen and a file (result.txt).	第一个参数=0表示以create方式创建和输出文件；否则以append方式输出文件；
                        else
                            PrintSolution(1, filename, hmethod, opensize, hFmethod, ep, ep2, elapsedTimeRunI, elapsedTimeTotal, runCount, f_upper, NExpandedNodeRunI, NExpandedNode, fileNameOutput[0]);

                        startTimeRunI = currentTime;


                        runCount++;
                        NExpandedNodeRunI = 0;

                        continue; //start a new iteration from while (FOpenList.Count > 0)
                    }


                    //把当前节点的所有子节点加入到FSuccessors  Add the child nodes of the current node to the list FSuccessors.
                    FSuccessors.Clear();
                    NodeCurrent.GetSuccessors(FSuccessors, hmethod, ep2, hValueStartNode);

                    NExpandedNodeRunI++; //Expanded states # in this run
                    NExpandedNode++; //Total expanded states #
                    //FExpandedList.Add(NodeCurrent);//是否需要？用于Debug


                    if (printScreen == true)
                        NodeCurrent.PrintNodeInfo(loop);//打印当前节点的信息 Print the node of the current node.
                    //    if (printScreen == true)
                    //if (loop==916)//loop >= 915 && loop <= 917)///
                    // {//
                    //             NodeCurrent.PrintNodeInfo(loop);//打印当前节点的信息
                    //   foreach (AStarNode a in FOpenList)//
                    //         {//
                    //    a.PrintNodeInfo(-1);//
                    //           }//
                    //   }//

                    foreach (AStarNode NodeSuccessor in FSuccessors)
                    {
                        if (NodeSuccessor.fValue < f_upper)
                        {


                            //如果子节点S'和OPEN中某节点S有相同M和Mr,但g'<g,则用S'替换Open中S 
                            //If the successor has the same M and R as a node in OPEN, but has smaller g-value, then delete the node and add the successor in OPEN in the non-decreasing oder of f.

                            AStarNode NodeOpen = null;


                            foreach (AStarNode anode in FOpenList)
                            {
                                if (anode.IsSameStatePlusMr(NodeSuccessor))
                                {
                                    NodeOpen = anode;
                                    break;
                                }
                            }

                            if (NodeOpen != null) //
                            {
                                if (NodeSuccessor.gValue < NodeOpen.gValue)
                                {
                                    FOpenList.Remove(NodeOpen);
                                    SortAdd(FOpenList, NodeSuccessor);
                                    //continue; //****!!!
                                }
                            }




                            //如果子节点S'和Closed中某节点S有相同M和Mr,但g'<g,则删掉CLOSED的S，并将S'插入到Open
                            //If the successor has the same M anr Mr as a node in CLOSED but has smaller g-value, then delete the node in Closed and insert the successor into OPEN in the non-decreasing order of f.
                            AStarNode NodeClosed = null;
                            foreach (AStarNode anode in FClosedList)
                            {
                                if (anode.IsSameStatePlusMr(NodeSuccessor))
                                {
                                    NodeClosed = anode;
                                    break;
                                }
                            }


                            if (NodeClosed != null)
                            {
                                if (NodeSuccessor.gValue < NodeClosed.gValue)
                                {
                                    FClosedList.Remove(NodeClosed);
                                    SortAdd(FOpenList, NodeSuccessor);
                                    continue;
                                }
                            }



                            //If there exists no state in OPEN and CLOSED as the successor, insert the successor into OPEN in the non-decreasing order of f. 
                            if (NodeOpen == null && NodeClosed == null)
                                SortAdd(FOpenList, NodeSuccessor); 

                        }

                                               
                    } //The end of foreach (AStarNode NodeSuccessor in FSuccessors)

                    SortAdd(FClosedList, NodeCurrent);                 

                    
                }//if (NodeCurrent.fValue < f_upper)             


            }// while (FOpenList.Count >= 0)

            Console.WriteLine();
            if (f_upper != infinity)
            {
                currentTime = DateTime.Now;                
                elapsedTimeTotal = new TimeSpan(currentTime.Ticks - startTimeTotal.Ticks);//总运行时间 the total running time
                PrintTimeExpandedNodes(elapsedTimeTotal, NExpandedNode, fileNameOutput[0]);//向文件result.txt输出最终时间和扩展节点数
                Console.WriteLine("The anytime A* search finnished with success! ");//向屏幕输出
            }
            else
                Console.WriteLine("The anytime A* search finnished with failure!");//向屏幕输出

            /*AStarNode FinalMarking = (AStarNode)FSolution[FSolution.Count - 1];

            decimal[] result = new decimal[4];
            result[0] = (decimal)FinalMarking.fValue;//最后结果的cost
            result[1] = (decimal)FExpandedList.Count;//最后EXPANDED表的长度
            result[2] = (decimal)FOpenList.Count;//最后OPEN表的长度
            result[3] = (decimal)FClosedList.Count;//最后CLOSE表的长度

            result[1] = NExpandedNode;
            Console.WriteLine("result:", result);
            for (int i = 0; i < 4; ++i)
            {
                Console.Write(result[i] + " ");
            }
            return result*/

        }//FindPath_AnytimeAstar

        #endregion
    }
}