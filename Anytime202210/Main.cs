using System;
using System.IO;
using System.Collections;
using Tanis.Collections;

namespace Huangbo.AStarPetri.Test
{
    class MainClass
    {

        #region Public Methods

        [STAThread]

        static void Main(string[] args)
        {
            /*
             * This program is to search a scheduling path from an initial state to a goal state in the reachability graph of a place-timed Petri net for a resource allocation system by using the A* search and its variants.
             * For the details on the implemented algorithms, please refer to our book: Bo Huang, MengChu Zhou, Supervisory Control and Scheduling of Resource Allocation Systems. Wiley-IEEE Press. 2020, and our papers.
             * For bug reports or information, please contact: huangbo@njust.edu.cn
             * March. 15, 2020
            */

            Huangbo.AStarPetri.AStar astar;
            Huangbo.AStarPetri.AStarNode GoalNode;
            Huangbo.AStarPetri.AStarNode StartNode;

            //string[] filenames = new string[] {"ChenFig511", "ChenFig522", "ChenFig533", "ChenFig544", "ChenFig555"};
            string[] filenames = new string[] { "Huang2012Fig1Revised2111", "Huang2012Fig1Revised2211", "Huang2012Fig1Revised2221", "Huang2012Fig1Revised2222" };
            //string[] filenames = new string[] { "Huang2012Fig1Revised1111", "Huang2012Fig1Revised2111", "Huang2012Fig1Revised2211", "Huang2012Fig1Revised2221", "Huang2012Fig1Revised2222" };
            //string[] filenames = new string[] { "Chen2011Big11112", "Chen2011Big11122", "Chen2011Big11222" }; //If h7=h_H is used, the number of resource places, the WRT matrix, the Upi matrix, and the M0r vector of the Petri net should be given in the class AStar.
            //string[] filenames = new string[] { "ChenFig6111", "ChenFig6222", "ChenFig6333", "ChenFig6444"};

            //string filename = "ChenFig544";  //The prefix of your input files.         The paper Huang2020 uses Huang2012Fig1Revised and ChenFig6111-ChenFig6444.   
            //string filename = "ChenFig6555";  //The prefix of your input files. 
            //string filename = "Chen2011Big11122";  //The prefix of your input files. 
 
  


            int[] hmethods = new int[]  { 7 };//所用启发函数h  //the used heuristic function, for example, if you want to use h=0, you input 2 here and if you want to use h=h_H, you input 7 here.
            //Note that before h1 and h9 are used, some parameters of the tested Petri net should be given in CalculateH() in AStar.cs. 
            //If h7 is used, the number of resource places, the WRT matrix, the Upi matrix, and the M0r vector of the tested Petri net should be given in the class AStar!!!!!!!!!!!!!!!!  Such a place for revisions is marked with: //Revised when h7 is used!!
            
            //h1=max{ei(m)} plus R; max{ei(m)} comes from Xiong98.
            //h2=0;
            //h4=-dep(m);
            //h7 = h_H=max{E[M(p_i)*WRT(pi,r)+ER(pi,x)*Upi(r)/M0(r)]} comes from Chapter 9 of our book and our pape: Bo Huang, et al. Scheduling Robotic Cellular Manufacturing Systems with Timed Petri Net, A* Search and Admissible Heuristic Function. IEEE Transactions on Automation Science and Engineering, Jan. 2022, 19(1): 243-250.;  
            //Before h7=h_H is used, the number of resource places, the WRT matrix, the Upi matrix, and the M0r vector of the Petri net should be given in the class AStar. 

            //h710(Pohl)=h+ep2*(1-dn/dG)*h, h=h7=h_H, 此时要在Calculate()中设置总深度N=dG=totalDepth！  大-小，线性
            //    (reversed Pohl)=h+ep2*(dn/dG)*h, h=h7=h_H, 此时要设置总深度N=dG=totalDepth！   小-大，线性
            //    (Pohl)=h+ep2*[1-dn/dG]^2*h, h=h7=h_H, 此时要设置总深度N=dG=totalDepth！   大-小，2次，凹
            //    (Pohl)=h+ep2*{1-[dn/dG]^2}*h, h=h7=h_H, 此时要设置总深度N=dG=totalDepth！   大-小，2次，凸
            //    (Pohl)=h+ep2*{1-0.5*[1-dn/dG]}*h,      0<= dn/dG <0.4;        h=h7=h_H, 此时要设置总深度dG=totalDepth！   大-小，线性，分3段函数
            //          =h+ep2*{2-3*[1-dn/dG]}*h,        0.4<= dn/dG <0.6;       
            //          =h+ep2*{0.5-0.5*[1-dn/dG]}*h,    0.6<= dn/dG <=1;
            //    (Pohl)=h+ep2*h,               0<= dn/dG <0.5;        h=h7=h_H, 此时要设置总深度dG=totalDepth！   大-小，线性，分2段函数
            //          =h+ep2*(2-2*dndG)*h,    0.5<= dn/dG <=1;   

            //h720(IDWA)=h+ep2*(h/h_0)*h, h=h7=h_H,  大-小，线性
            //h721(IDWA)=h+ep2*[1-h/h_0]*h, h=h7=h_H,    小-大，线性
            //h722(IDWA)=h+ep2*[h/h_0]^2*h, h=h7=h_H,  大-小，2次，凹
            //h723(IDWA)=h+ep2*{1-[1-h/h_0]^2}*h, h=h7=h_H, 大-小，2次，凸

            //h9=hs+max{ei(m)}+he in which max{ei(m)} comes from Xiong98, hs denotes the necessary time before the resource is used, and he denotes the necessary time after the resource is used.


            int[] opensizes = new int[1] { 0 };//opensize:0:表示open可为无穷大；大于0：表示进行BF locally,BT globally
            //opensize: the maximal number of nodes in OPEN. 
            //opensize=0 denotes unlimited. opensize>0 denotes the A* search will use the BF locally and BT globally as described in Chapter 10 of our book.


            //decimal[] eps = new decimal[] { 0.2m, 0.8m };//Original A* 
            //decimal[] eps = new decimal[] { 0m, 0.2m, 0.5m, 0.8m };
            decimal[] eps = new decimal[] { 0.2m, 0.5m, 0.8m };
            //ep: the parameter epsilon used in Chapter 9 of our book.It is for selecting a markings in OPEN for expansion! Not affecting the calculations of h. 
            //ep<0时相当于没有ep的情况  ep<0 indicates the A* search does not use the epsilon. 
            //ep=0时，选OPEN中具有相同最小f值marking中有最小hFCost的(0比-1好)
            //ep>0时选择范围更大,选OPEN中具有不大于最小f值1+ep倍的marking中有最小hFCost的. 即SELECT={S|f(S)<=(1+ep)*f(S^1_OPEN)}
            //ep>=0 indicates the A* search picks out the node with the minimal hFCost value for expansion among the nodes having the f-value between f_min and f_min*(1+ep) in OPEN.


            int hFmethod = 2;	//所用第二个启发函数，用于对OPEN中的节点进行二次排序  It is used for e-A*; The second hueristic function is for the states in OPEN.
            //1=h;2=-(FMarkingDepth+1);10=h;
            //从小到大排序


            //decimal[] ep2s = new decimal[] { 0m, 0.1m, 0.2m, 0.3m, 0.4m, 0.5m, 0.6m, 0.7m, 0.8m, 0.9m, 1m };            
            decimal[] ep2s = new decimal[] { 0m };
            //It is only for calculating h in dynamic weighted searches (for h710, h720-723.), e.g., h710=h+ep2*(1-dn/dG)*h. pe2s={0m},0表示无意义，无循环 ；如果需要运行多次不同情况，ep2s={0m, 0.01m, 0.05m, 0.1m}. 


            bool printScreen = true;//是否向屏幕打印每个扩展节点的信息   Whether or not to print each expanded node to your screen.


            foreach (string filename in filenames)
            {
                string[] initfile = new string[] { "./" + filename + "_init.txt" };
                string[] matrixfile = new string[] { "./" + filename + "_matrix.txt" };
                
                foreach (int hmethod in hmethods)
                {
                    foreach (int opensize in opensizes)
                    {
                        for (int j = 0; j < eps.Length; j++)
                        {
                            decimal ep = eps[j];
                            for (int i = 0; i < ep2s.Length; i++)
                            {
                                decimal ep2 = ep2s[i];

                                astar = new Huangbo.AStarPetri.AStar(initfile[0], matrixfile[0]);
                                GoalNode = new Huangbo.AStarPetri.AStarNode(null, null, 0, 0, 0, AStar.GoalM, AStar.GoalMr, 0, 0, 0, 0);
                                StartNode = new Huangbo.AStarPetri.AStarNode(null, GoalNode, 0, 0, 0, AStar.StartM, AStar.StartMr, 0, 0, 0, 0);

                                Console.WriteLine();
                                Console.WriteLine("hmethod={0},filename={1},filename={2},running...", hmethod, initfile[0], matrixfile[0]);


                                astar.FindPath_AnytimeAstar(StartNode, GoalNode, ep, ep2, hmethod, hFmethod, opensize, printScreen, filename);


                            }
                        }

                    }
                }
            
            }

            Console.ReadLine(); //保持输出屏幕不被关闭
        }

        #endregion
    }
}