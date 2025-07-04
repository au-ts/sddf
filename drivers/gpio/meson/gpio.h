/*
 * Copyright 2024, UNSW
 * SPDX-License-Identifier: BSD-2-Clause
 */

#include <stdint.h>	

/*
=======
linux/include/dt-bindings/interrupt-controller/amlogic,meson-g12a-gpio-intc.h
=======
*/

// Note these bindings are so that its compatible with what goes into the
// IRQ pin select register
// It is not what the linux DTS actually specifies

/* IRQID[11:0] - GPIOAO[11:0] */
#define IRQID_GPIOAO_0		0
#define IRQID_GPIOAO_1		1
#define IRQID_GPIOAO_2		2
#define IRQID_GPIOAO_3		3
#define IRQID_GPIOAO_4		4
#define IRQID_GPIOAO_5		5
#define IRQID_GPIOAO_6		6
#define IRQID_GPIOAO_7		7
#define IRQID_GPIOAO_8		8
#define IRQID_GPIOAO_9		9
#define IRQID_GPIOAO_10		10
#define IRQID_GPIOAO_11		11

/* IRQID[27:12] - GPIOZ[15:0] */
#define IRQID_GPIOZ_0		12
#define IRQID_GPIOZ_1		13
#define IRQID_GPIOZ_2		14
#define IRQID_GPIOZ_3		15
#define IRQID_GPIOZ_4		16
#define IRQID_GPIOZ_5		17
#define IRQID_GPIOZ_6		18
#define IRQID_GPIOZ_7		19
#define IRQID_GPIOZ_8		20
#define IRQID_GPIOZ_9		21
#define IRQID_GPIOZ_10		22
#define IRQID_GPIOZ_11		23
#define IRQID_GPIOZ_12		24
#define IRQID_GPIOZ_13		25
#define IRQID_GPIOZ_14		26
#define IRQID_GPIOZ_15		27

/* IRQID[36:28] - GPIOH[8:0] */
#define IRQID_GPIOH_0		28
#define IRQID_GPIOH_1		29
#define IRQID_GPIOH_2		30
#define IRQID_GPIOH_3		31
#define IRQID_GPIOH_4		32
#define IRQID_GPIOH_5		33
#define IRQID_GPIOH_6		34
#define IRQID_GPIOH_7		35
#define IRQID_GPIOH_8		36

/* IRQID[52:37] - BOOT[15:0] */
#define IRQID_BOOT_0		37
#define IRQID_BOOT_1		38
#define IRQID_BOOT_2		39
#define IRQID_BOOT_3		40
#define IRQID_BOOT_4		41
#define IRQID_BOOT_5		42
#define IRQID_BOOT_6		43
#define IRQID_BOOT_7		44
#define IRQID_BOOT_8		45
#define IRQID_BOOT_9		46
#define IRQID_BOOT_10		47
#define IRQID_BOOT_11		48
#define IRQID_BOOT_12		49
#define IRQID_BOOT_13		50
#define IRQID_BOOT_14		51
#define IRQID_BOOT_15		52

/* IRQID[60:53] - GPIOC[7:0] */
#define IRQID_GPIOC_0		53
#define IRQID_GPIOC_1		54
#define IRQID_GPIOC_2		55
#define IRQID_GPIOC_3		56
#define IRQID_GPIOC_4		57
#define IRQID_GPIOC_5		58
#define IRQID_GPIOC_6		59
#define IRQID_GPIOC_7		60

/* IRQID[76:61] - GPIOA[15:0] */
#define IRQID_GPIOA_0		61
#define IRQID_GPIOA_1		62
#define IRQID_GPIOA_2		63
#define IRQID_GPIOA_3		64
#define IRQID_GPIOA_4		65
#define IRQID_GPIOA_5		66
#define IRQID_GPIOA_6		67
#define IRQID_GPIOA_7		68
#define IRQID_GPIOA_8		69
#define IRQID_GPIOA_9		70
#define IRQID_GPIOA_10		71
#define IRQID_GPIOA_11		72
#define IRQID_GPIOA_12		73
#define IRQID_GPIOA_13		74
#define IRQID_GPIOA_14		75
#define IRQID_GPIOA_15		76

/* IRQID[96:77] - GPIOX[19:0] */
#define IRQID_GPIOX_0		77
#define IRQID_GPIOX_1		78
#define IRQID_GPIOX_2		79
#define IRQID_GPIOX_3		80
#define IRQID_GPIOX_4		81
#define IRQID_GPIOX_5		82
#define IRQID_GPIOX_6		83
#define IRQID_GPIOX_7		84
#define IRQID_GPIOX_8		85
#define IRQID_GPIOX_9		86
#define IRQID_GPIOX_10		87
#define IRQID_GPIOX_11		88
#define IRQID_GPIOX_12		89
#define IRQID_GPIOX_13		90
#define IRQID_GPIOX_14		91
#define IRQID_GPIOX_15		92
#define IRQID_GPIOX_16		93
#define IRQID_GPIOX_17		94
#define IRQID_GPIOX_18		95
#define IRQID_GPIOX_19		96

/* IRQID[99:97] - GPIOE[2:0] */
#define IRQID_GPIOE_0		97
#define IRQID_GPIOE_1		98
#define IRQID_GPIOE_2		99

/*
=======
linux/include/dt-bindings/gpio/meson-g12a-gpio.h
=======
*/

// This file also has a scheme for numbering the GPIOs which is how the
// DTS defines them however it has a different numbering scheme for the 2 banks
// 1 for AO gpios and one for peripheral gpios
// thus for now since we do not need to know the specific gpios in the DTS
// we just use the irqid_gpio scheme for everything
// these are the ones that actually appear inside the d

// /* First GPIO chip */
// #define GPIOAO_0	0
// #define GPIOAO_1	1
// #define GPIOAO_2	2
// #define GPIOAO_3	3
// #define GPIOAO_4	4
// #define GPIOAO_5	5
// #define GPIOAO_6	6
// #define GPIOAO_7	7
// #define GPIOAO_8	8
// #define GPIOAO_9	9
// #define GPIOAO_10	10
// #define GPIOAO_11	11
// #define GPIOE_0		12
// #define GPIOE_1		13
// #define GPIOE_2		14

// /* Second GPIO chip */
// #define GPIOZ_0		0
// #define GPIOZ_1		1
// #define GPIOZ_2		2
// #define GPIOZ_3		3
// #define GPIOZ_4		4
// #define GPIOZ_5		5
// #define GPIOZ_6		6
// #define GPIOZ_7		7
// #define GPIOZ_8		8
// #define GPIOZ_9		9
// #define GPIOZ_10	10
// etc...

/*
=======
linux/drivers/pinctrl/meson/pinctrl-meson.h
=======
*/

/**
 * struct meson_reg_desc - a register descriptor
 *
 * @reg:	register offset in the regmap
 * @bit:	bit index in register
 *
 * The structure describes the information needed to control pull,
 * pull-enable, direction, etc. for a single pin
 */
struct meson_reg_desc {
	unsigned int reg;
	unsigned int bit;
};

/**
 * enum meson_reg_type - type of registers encoded in @meson_reg_desc
 */
enum meson_reg_type {
	MESON_REG_PULLEN,
	MESON_REG_PULL,
	MESON_REG_DIR,
	MESON_REG_OUT,
	MESON_REG_IN,
	MESON_REG_DS,
	MESON_NUM_REG,
};

/**
 * enum meson_pinconf_drv - value of drive-strength supported
 */
// enum meson_pinconf_drv {
// 	MESON_PINCONF_DRV_500UA,
// 	MESON_PINCONF_DRV_2500UA,
// 	MESON_PINCONF_DRV_3000UA,
// 	MESON_PINCONF_DRV_4000UA,
// };

/**
 * struct meson bank
 *
 * @name:	bank name
 * @first:	first pin of the bank
 * @last:	last pin of the bank
 * @irq:	hwirq base number of the bank
 * @regs:	array of register descriptors
 *
 * A bank represents a set of pins controlled by a contiguous set of
 * bits in the domain registers. The structure specifies which bits in
 * the regmap control the different functionalities. Each member of
 * the @regs array refers to the first pin of the bank.
 */
struct meson_bank {
	const char *name;
	unsigned int first;
	unsigned int last;
	struct meson_reg_desc regs[MESON_NUM_REG];
};

struct meson_pinctrl_data {
	const char *name;
	const struct pinctrl_pin_desc *pins;
	unsigned int num_pins;
	const struct meson_bank *banks;
	unsigned int num_banks;
};

#define BANK_DS(n, f, l, per, peb, pr, pb, dr, db, or, ob, ir, ib,     \
		dsr, dsb)                                                      \
	{								\
		.name		= n,					\
		.first		= f,					\
		.last		= l,					\
		.regs = {						\
			[MESON_REG_PULLEN]	= { per, peb },		\
			[MESON_REG_PULL]	= { pr, pb },		\
			[MESON_REG_DIR]		= { dr, db },		\
			[MESON_REG_OUT]		= { or, ob },		\
			[MESON_REG_IN]		= { ir, ib },		\
			[MESON_REG_DS]		= { dsr, dsb },		\
		},							\
	 }


// #define BANK(n, f, l, per, peb, pr, pb, dr, db, or, ob, ir, ib) \
// 	BANK_DS(n, f, l, per, peb, pr, pb, dr, db, or, ob, ir, ib, 0, 0)

/*
=======
linux/drivers/pinctrl/meson/pinctrl-meson-g12a.c
=======
*/

static const struct meson_bank meson_g12a_periphs_banks[] = {
	/* name  first  last  irq  pullen  pull  dir  out  in  ds */
	BANK_DS("Z",  IRQID_GPIOZ_0,  IRQID_GPIOZ_15,
		4,  0,  4,  0,  12,  0, 13,  0,  14,  0,  5, 0),
	BANK_DS("H",  IRQID_GPIOH_0,  IRQID_GPIOH_8,
		3,  0,  3,  0,   9,  0, 10,  0,  11,  0,  4, 0),
	BANK_DS("BOOT",  IRQID_BOOT_0,   IRQID_BOOT_15,
		0,  0,  0,  0,   0,  0,  1,  0,   2,  0,  0, 0),
	BANK_DS("C",  IRQID_GPIOC_0,  IRQID_GPIOC_7,
		1,  0,  1,  0,   3,  0,  4,  0,   5,  0,  1, 0),
	BANK_DS("A",  IRQID_GPIOA_0,  IRQID_GPIOA_15,
		5,  0,  5,  0,  16,  0, 17,  0,  18,  0,  6, 0),
	BANK_DS("X",  IRQID_GPIOX_0,  IRQID_GPIOX_19,
		2,  0,  2,  0,   6,  0,  7,  0,   8,  0,  2, 0),
};

static const struct meson_bank meson_g12a_aobus_banks[] = {
	/* name  first  last  irq  pullen  pull  dir  out  in  ds */
	BANK_DS("AO",  IRQID_GPIOAO_0, IRQID_GPIOAO_11,
		3,  0,  2,  0,   0,  0,  4,  0,   1,  0,  0, 0),
	/* GPIOE actually located in the AO bank */
	BANK_DS("E",  IRQID_GPIOE_0,  IRQID_GPIOE_2,
		3, 16,  2, 16,   0, 16,  4, 16,   1, 16,  1, 0),
};

static const struct meson_pinctrl_data meson_g12a_periphs_pinctrl_data = {
	.name		= "periphs-banks",
	// .pins		= meson_g12a_periphs_pins,
	// .groups		= meson_g12a_periphs_groups,
	// .funcs		= meson_g12a_periphs_functions,
	.banks		= meson_g12a_periphs_banks,
	// .num_pins	= ARRAY_SIZE(meson_g12a_periphs_pins),
	// .num_groups	= ARRAY_SIZE(meson_g12a_periphs_groups),
	// .num_funcs	= ARRAY_SIZE(meson_g12a_periphs_functions),
	.num_banks	= ARRAY_SIZE(meson_g12a_periphs_banks),
	// .pmx_ops	= &meson_axg_pmx_ops,
	// .pmx_data	= &meson_g12a_periphs_pmx_banks_data,
};

static const struct meson_pinctrl_data meson_g12a_aobus_pinctrl_data = {
	.name		= "aobus-banks",
	// .pins		= meson_g12a_aobus_pins,
	// .groups		= meson_g12a_aobus_groups,
	// .funcs		= meson_g12a_aobus_functions,
	.banks		= meson_g12a_aobus_banks,
	// .num_pins	= ARRAY_SIZE(meson_g12a_aobus_pins),
	// .num_groups	= ARRAY_SIZE(meson_g12a_aobus_groups),
	// .num_funcs	= ARRAY_SIZE(meson_g12a_aobus_functions),
	.num_banks	= ARRAY_SIZE(meson_g12a_aobus_banks),
	// .pmx_ops	= &meson_axg_pmx_ops,
	// .pmx_data	= &meson_g12a_aobus_pmx_banks_data,
	// .parse_dt	= meson_g12a_aobus_parse_dt_extra,
};
