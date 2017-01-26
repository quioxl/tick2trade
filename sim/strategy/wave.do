onerror {resume}
radix define Cmds {
    "8'h01" "RESET" -color "red",
    "8'h02" "LOAD" -color "blue",
    -default hexadecimal
    -defaultcolor white
}
radix define Rams {
    "8'h01" "SYMBOL" -color "red",
    "8'h02" "PRICE" -color "blue",
    "8'h04" "VOLUME" -color "green",
    "8'h08" "ORDER" -color "orange",
    -default hexadecimal
    -defaultcolor white
}
quietly virtual function -install /tb/host_if -env /tb/host_if { &{ sim:/tb/host_if/in_config_data(255), sim:/tb/host_if/in_config_data(254), sim:/tb/host_if/in_config_data(253), sim:/tb/host_if/in_config_data(252), sim:/tb/host_if/in_config_data(251), sim:/tb/host_if/in_config_data(250), sim:/tb/host_if/in_config_data(249), sim:/tb/host_if/in_config_data(248) }} host_cmd
quietly virtual function -install /tb/host_if -env /tb/host_if { &{ sim:/tb/host_if/in_config_data(247), sim:/tb/host_if/in_config_data(246), sim:/tb/host_if/in_config_data(245), sim:/tb/host_if/in_config_data(244), sim:/tb/host_if/in_config_data(243), sim:/tb/host_if/in_config_data(242), sim:/tb/host_if/in_config_data(241), sim:/tb/host_if/in_config_data(240) }} host_ram
quietly virtual function -install /tb/host_if -env /tb/host_if { &{ sim:/tb/host_if/in_config_data(239), sim:/tb/host_if/in_config_data(238), sim:/tb/host_if/in_config_data(237), sim:/tb/host_if/in_config_data(236), sim:/tb/host_if/in_config_data(235), sim:/tb/host_if/in_config_data(234), sim:/tb/host_if/in_config_data(233), sim:/tb/host_if/in_config_data(232), sim:/tb/host_if/in_config_data(231), sim:/tb/host_if/in_config_data(230), sim:/tb/host_if/in_config_data(229), sim:/tb/host_if/in_config_data(228), sim:/tb/host_if/in_config_data(227), sim:/tb/host_if/in_config_data(226), sim:/tb/host_if/in_config_data(225), sim:/tb/host_if/in_config_data(224) }} host_addr
quietly virtual function -install /tb/host_if -env /tb/host_if { &{ sim:/tb/host_if/in_config_data(215), sim:/tb/host_if/in_config_data(214), sim:/tb/host_if/in_config_data(213), sim:/tb/host_if/in_config_data(212), sim:/tb/host_if/in_config_data(211), sim:/tb/host_if/in_config_data(210), sim:/tb/host_if/in_config_data(209), sim:/tb/host_if/in_config_data(208), sim:/tb/host_if/in_config_data(207), sim:/tb/host_if/in_config_data(206), sim:/tb/host_if/in_config_data(205), sim:/tb/host_if/in_config_data(204), sim:/tb/host_if/in_config_data(203), sim:/tb/host_if/in_config_data(202), sim:/tb/host_if/in_config_data(201), sim:/tb/host_if/in_config_data(200), sim:/tb/host_if/in_config_data(199), sim:/tb/host_if/in_config_data(198), sim:/tb/host_if/in_config_data(197), sim:/tb/host_if/in_config_data(196), sim:/tb/host_if/in_config_data(195), sim:/tb/host_if/in_config_data(194), sim:/tb/host_if/in_config_data(193), sim:/tb/host_if/in_config_data(192) }} host_byte_en
quietly virtual function -install /tb/host_if -env /tb/host_if { &{ sim:/tb/host_if/in_config_data(127), sim:/tb/host_if/in_config_data(126), sim:/tb/host_if/in_config_data(125), sim:/tb/host_if/in_config_data(124), sim:/tb/host_if/in_config_data(123), sim:/tb/host_if/in_config_data(122), sim:/tb/host_if/in_config_data(121), sim:/tb/host_if/in_config_data(120), sim:/tb/host_if/in_config_data(119), sim:/tb/host_if/in_config_data(118), sim:/tb/host_if/in_config_data(117), sim:/tb/host_if/in_config_data(116), sim:/tb/host_if/in_config_data(115), sim:/tb/host_if/in_config_data(114), sim:/tb/host_if/in_config_data(113), sim:/tb/host_if/in_config_data(112), sim:/tb/host_if/in_config_data(111), sim:/tb/host_if/in_config_data(110), sim:/tb/host_if/in_config_data(109), sim:/tb/host_if/in_config_data(108), sim:/tb/host_if/in_config_data(107), sim:/tb/host_if/in_config_data(106), sim:/tb/host_if/in_config_data(105), sim:/tb/host_if/in_config_data(104), sim:/tb/host_if/in_config_data(103), sim:/tb/host_if/in_config_data(102), sim:/tb/host_if/in_config_data(101), sim:/tb/host_if/in_config_data(100), sim:/tb/host_if/in_config_data(99), sim:/tb/host_if/in_config_data(98), sim:/tb/host_if/in_config_data(97), sim:/tb/host_if/in_config_data(96), sim:/tb/host_if/in_config_data(95), sim:/tb/host_if/in_config_data(94), sim:/tb/host_if/in_config_data(93), sim:/tb/host_if/in_config_data(92), sim:/tb/host_if/in_config_data(91), sim:/tb/host_if/in_config_data(90), sim:/tb/host_if/in_config_data(89), sim:/tb/host_if/in_config_data(88), sim:/tb/host_if/in_config_data(87), sim:/tb/host_if/in_config_data(86), sim:/tb/host_if/in_config_data(85), sim:/tb/host_if/in_config_data(84), sim:/tb/host_if/in_config_data(83), sim:/tb/host_if/in_config_data(82), sim:/tb/host_if/in_config_data(81), sim:/tb/host_if/in_config_data(80), sim:/tb/host_if/in_config_data(79), sim:/tb/host_if/in_config_data(78), sim:/tb/host_if/in_config_data(77), sim:/tb/host_if/in_config_data(76), sim:/tb/host_if/in_config_data(75), sim:/tb/host_if/in_config_data(74), sim:/tb/host_if/in_config_data(73), sim:/tb/host_if/in_config_data(72), sim:/tb/host_if/in_config_data(71), sim:/tb/host_if/in_config_data(70), sim:/tb/host_if/in_config_data(69), sim:/tb/host_if/in_config_data(68), sim:/tb/host_if/in_config_data(67), sim:/tb/host_if/in_config_data(66), sim:/tb/host_if/in_config_data(65), sim:/tb/host_if/in_config_data(64), sim:/tb/host_if/in_config_data(63), sim:/tb/host_if/in_config_data(62), sim:/tb/host_if/in_config_data(61), sim:/tb/host_if/in_config_data(60), sim:/tb/host_if/in_config_data(59), sim:/tb/host_if/in_config_data(58), sim:/tb/host_if/in_config_data(57), sim:/tb/host_if/in_config_data(56), sim:/tb/host_if/in_config_data(55), sim:/tb/host_if/in_config_data(54), sim:/tb/host_if/in_config_data(53), sim:/tb/host_if/in_config_data(52), sim:/tb/host_if/in_config_data(51), sim:/tb/host_if/in_config_data(50), sim:/tb/host_if/in_config_data(49), sim:/tb/host_if/in_config_data(48), sim:/tb/host_if/in_config_data(47), sim:/tb/host_if/in_config_data(46), sim:/tb/host_if/in_config_data(45), sim:/tb/host_if/in_config_data(44), sim:/tb/host_if/in_config_data(43), sim:/tb/host_if/in_config_data(42), sim:/tb/host_if/in_config_data(41), sim:/tb/host_if/in_config_data(40), sim:/tb/host_if/in_config_data(39), sim:/tb/host_if/in_config_data(38), sim:/tb/host_if/in_config_data(37), sim:/tb/host_if/in_config_data(36), sim:/tb/host_if/in_config_data(35), sim:/tb/host_if/in_config_data(34), sim:/tb/host_if/in_config_data(33), sim:/tb/host_if/in_config_data(32), sim:/tb/host_if/in_config_data(31), sim:/tb/host_if/in_config_data(30), sim:/tb/host_if/in_config_data(29), sim:/tb/host_if/in_config_data(28), sim:/tb/host_if/in_config_data(27), sim:/tb/host_if/in_config_data(26), sim:/tb/host_if/in_config_data(25), sim:/tb/host_if/in_config_data(24), sim:/tb/host_if/in_config_data(23), sim:/tb/host_if/in_config_data(22), sim:/tb/host_if/in_config_data(21), sim:/tb/host_if/in_config_data(20), sim:/tb/host_if/in_config_data(19), sim:/tb/host_if/in_config_data(18), sim:/tb/host_if/in_config_data(17), sim:/tb/host_if/in_config_data(16), sim:/tb/host_if/in_config_data(15), sim:/tb/host_if/in_config_data(14), sim:/tb/host_if/in_config_data(13), sim:/tb/host_if/in_config_data(12), sim:/tb/host_if/in_config_data(11), sim:/tb/host_if/in_config_data(10), sim:/tb/host_if/in_config_data(9), sim:/tb/host_if/in_config_data(8), sim:/tb/host_if/in_config_data(7), sim:/tb/host_if/in_config_data(6), sim:/tb/host_if/in_config_data(5), sim:/tb/host_if/in_config_data(4), sim:/tb/host_if/in_config_data(3), sim:/tb/host_if/in_config_data(2), sim:/tb/host_if/in_config_data(1), sim:/tb/host_if/in_config_data(0) }} host_data
quietly WaveActivateNextPane {} 0
add wave -noupdate -expand -group {Feed Interface} /tb/feed_if/clk
add wave -noupdate -expand -group {Feed Interface} /tb/feed_if/reset_n
add wave -noupdate -expand -group {Feed Interface} /tb/feed_if/ready
add wave -noupdate -expand -group {Feed Interface} /tb/feed_if/valid
add wave -noupdate -expand -group {Feed Interface} /tb/feed_if/startofpacket
add wave -noupdate -expand -group {Feed Interface} /tb/feed_if/endofpacket
add wave -noupdate -expand -group {Feed Interface} /tb/feed_if/data
add wave -noupdate -expand -group {Feed Interface} /tb/feed_if/empty
add wave -noupdate -expand -group {Feed Interface} /tb/feed_if/error
add wave -noupdate -expand -group {Host Interface} /tb/host_if/clk
add wave -noupdate -expand -group {Host Interface} /tb/host_if/reset_n
add wave -noupdate -expand -group {Host Interface} /tb/host_if/in_config_valid
add wave -noupdate -expand -group {Host Interface} /tb/host_if/in_config_data
add wave -noupdate -expand -group {Host Interface} -radix Cmds /tb/host_if/host_cmd
add wave -noupdate -expand -group {Host Interface} -radix Rams /tb/host_if/host_ram
add wave -noupdate -expand -group {Host Interface} /tb/host_if/host_addr
add wave -noupdate -expand -group {Host Interface} /tb/host_if/host_byte_en
add wave -noupdate -expand -group {Host Interface} /tb/host_if/host_data
add wave -noupdate -expand -group {Host Interface} /tb/host_if/in_config_accept
add wave -noupdate -expand -group {Order Interface} /tb/order_if/clk
add wave -noupdate -expand -group {Order Interface} /tb/order_if/reset_n
add wave -noupdate -expand -group {Order Interface} /tb/order_if/data
add wave -noupdate -expand -group {Order Interface} /tb/order_if/ready
add wave -noupdate -expand -group {Order Interface} /tb/order_if/valid
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {11535233 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 220
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 2
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns
update
WaveRestoreZoom {14509 ps} {230831 ps}
